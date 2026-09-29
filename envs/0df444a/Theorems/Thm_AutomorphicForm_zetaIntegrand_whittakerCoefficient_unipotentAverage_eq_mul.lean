-- Prove2me | Theorems.Thm_AutomorphicForm_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul
-- name    : AutomorphicForm.zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/d9060558-715e-5a77-bcbd-68ce87d61ded
-- title:
--   Unipotent Schwartz averaging multiplies the zeta integrand by int Bψ
-- statement:
--   Let $F$ be a number field, $D$ an arbitrary subset of $\mathrm{GL}_2(\mathbb A_F)$, and let $\psi$ be an additive character of $\mathbb A_F$ which is trivial on the image of $F$, continuous and nontrivial. Let $G\colon \mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be continuous, satisfy a moderate-growth bound $\|G(g)\|\le C\cdot\max(\|\det g\|,\|\det g\|^{-1})^M$ for some real $C$ and natural $M$ (with $\|\cdot\|$ the idele norm given by the module of the adelic Haar measure), and be invariant under left translation by the unipotents $n(\beta)=\begin{pmatrix}1&\beta\\0&1\end{pmatrix}$ for $\beta\in F$. Let $B$ lie in the Schwartz–Bruhat space of $\mathbb A_F$ (the $\mathbb C$-span of the pure tensors), let $\Phi(h)=\int B(x)\,G(h\,n(x))\,dx$ against adelic Haar measure, let $\chi$ be a homomorphism $\mathbb A_F^\times\to\mathbb C^\times$, $s\in\mathbb C$ and $a\in\mathbb A_F^\times$. Write $W_\phi(g)=\int \phi(n(x)g)\,\psi(-x)\,d\nu(x)$ for the Whittaker coefficient at $\alpha=1$ taken with respect to the production pins over $D$ with level groups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}_v$ and additive measure $\nu$ the adelic Haar measure conditioned on the adelic box. Then the zeta integrand $g\mapsto W_\Phi(\mathrm{diag}(a,1))\chi(a)\|a\|^{s-1}$ equals $\bigl(\int B(x)\psi(ax)\,dx\bigr)$ times the corresponding zeta integrand formed from $W_G$.
--
--   This is the multiplier identity for the Kirillov-type action of the unipotent group on the restriction of a Whittaker function to the torus, recorded at the level of the Tate zeta integrand $W(\mathrm{diag}(a,1))\chi(a)\|a\|^{s-1}$. It feeds the construction of test vectors whose $S$-part zeta integrand is entire and nonvanishing ([`AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero`](thm.html#AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul.lean

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

theorem AutomorphicForm.zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hGc : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (hGleft : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F), G (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = G g)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) :
    zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s a =
      (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * ψ (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)) *
      zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s a := by sorry
