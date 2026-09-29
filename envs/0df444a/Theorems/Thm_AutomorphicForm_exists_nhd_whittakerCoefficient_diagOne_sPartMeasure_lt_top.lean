-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top
-- name    : AutomorphicForm.exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/10893996-98ad-52c8-86d3-eb50bb64870d
-- title:
--   A finite-measure neighbourhood where the zeta integrand stays nonzero
-- statement:
--   Let $F$ be a number field, $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, and $\psi$ an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is `IsGlobalAddChar`, i.e. principal-invariant, continuous and nontrivial. Let $G \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and of moderate growth in the sense that for some $C \in \mathbb{R}$ and $M \in \mathbb{N}$ one has $\|G(g)\| \le C\,\max(\|\det g\|, \|\det g\|^{-1})^M$ for all $g$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character. Let $\chi \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be a continuous homomorphism trivial on the principal ideles $F^\times$, let $S$ be a finite set of finite places, let $a_0$ be an idele whose finite component is $1$ at every $v \notin S$, and let $s_1 \in \mathbb{C}$. Write $W(g)$ for the Whittaker coefficient of $G$ at $\alpha = 1$ against $\psi$, that is $\int G(u(x)g)\,\psi(-x)\,d\nu(x)$ with $\nu$ the adelic additive Haar measure conditioned on `adelicBox F`, taken for the production pins of $D$ with level groups $a \mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup` and Hecke generators `heckeGen`, and put $Z(s,a) = W(\mathrm{diag}(a,1))\,\chi(a)\,\|a\|^{s-1}$. Assume $W(\mathrm{diag}(a_0,1)) \neq 0$. Then there are sets $\Omega, K, N \subseteq \mathbb{A}_F^\times$ and reals $r, R, M_1, X$ such that: $\Omega$ and $K$ are Borel; $\nu_S(\Omega^c) = 0$ and $\nu_S(K) < \infty$ for the $S$-part measure $\nu_S$, the push-forward along `partAt F S` of idelic Haar measure restricted to the ideles that are units outside $S$; $r > 0$; $N$ is open with $a_0 \in N \subseteq K$; for every $s$ the function $a \mapsto Z(s,a)$ is Borel measurable; every $a \in K$ satisfies $\|W(\mathrm{diag}(a,1))\| \le M_1$, $\|\chi(a)\| \le X$ and $r \le \|a\| \le R$; $Z(s_1,a_0) \neq 0$; every $a \in \Omega \cap N$ satisfies $\tfrac12\|Z(s_1,a_0)\|^2 \le \operatorname{Re}\bigl(Z(s_1,a)\,\overline{Z(s_1,a_0)}\bigr)$; and $\Omega$ is exactly the fixed-point set of `partAt F S`.
--
--   This packages the local data needed to run a Tate-style zeta integral of the Whittaker coefficient along the diagonal torus: a Borel set of full $S$-part measure, a finite-measure set carrying uniform bounds on the Whittaker values, on $\chi$ and on the idele norm, and a neighbourhood of $a_0$ on which the integrand stays in a half-plane about its nonzero value at $a_0$. It is used by [`AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero`](thm.html#AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero), and rests on continuity of the Whittaker coefficient and of the idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem AutomorphicForm.exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hGc : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (s₁ : ℂ)
    (hW : whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 (diagOne a₀) ≠ 0) :
    ∃ (Ω K N : Set (AdeleRing (𝓞 F) F)ˣ) (r R M₁ X : ℝ),
      MeasurableSet[NumberField.Idele.ideleBorel F] Ω ∧ MeasurableSet[NumberField.Idele.ideleBorel F] K ∧ NumberField.Idele.sPartMeasure F S Ωᶜ = 0 ∧ NumberField.Idele.sPartMeasure F S K < ⊤ ∧ 0 < r ∧
      IsOpen N ∧ a₀ ∈ N ∧ N ⊆ K ∧
      (∀ s : ℂ, Measurable[NumberField.Idele.ideleBorel F] fun a => zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s a) ∧
      (∀ a ∈ K, ‖whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 (diagOne a)‖ ≤ M₁ ∧ ‖((χ a : ℂˣ) : ℂ)‖ ≤ X ∧ r ≤ ideleNorm F a ∧ ideleNorm F a ≤ R) ∧
      zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s₁ a₀ ≠ 0 ∧
      (∀ a ∈ Ω, a ∈ N →
        ‖zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ G 1 g) χ s₁ a₀‖ ^ 2 / 2 ≤
        (zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ G 1 g) χ s₁ a *
         star (zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ G 1 g) χ s₁ a₀)).re) ∧
      (∀ a, NumberField.Idele.partAt F S a = a ↔ a ∈ Ω) := by sorry
