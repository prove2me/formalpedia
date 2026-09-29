-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family
-- name    : AutomorphicForm.integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/78225b78-f028-552a-b66e-2bc857ded164
-- title:
--   Axis pairings of a Paley–Wiener family: integrability and reflection
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the ideles $(\mathbb{A}_F)^\times$ with values in $\mathbb{R}^\times$ obtained from the module (distributive Haar) character of $\mathbb{A}_F$ via $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed everywhere positive. Let $\iota$ be a finite index set and $\mu,\nu:\iota\to \operatorname{Hom}((\mathbb{A}_F)^\times,\mathbb{C}^\times)$ families of characters such that each $\mu_e,\nu_e$ has values of absolute value $1$, is trivial on the principal ideles $F^\times$, and is continuous; let $r:\iota\to\iota$ satisfy $\mu_{re}=\nu_e$ and $\nu_{re}=\mu_e$, and assume that for $e\neq e'$ some idele in the kernel of the module character separates the pairs, i.e. $\mu_e x\neq\mu_{e'}x$ or $\nu_e x\neq\nu_{e'}x$. Let $\psi_e(s):\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: $\psi_e(s)(bg)=\eta_1(b_{11})\eta_2(b_{22})\psi_e(s)(g)$ for $b$ with vanishing lower-left entry, where $\eta_1=\mu_e\,\alpha^{s+1/2}$ and $\eta_2=\nu_e\,\alpha^{-(s+1/2)}$; joint continuity in $(s,g)$; holomorphy in $s$; at each infinite place $w$ the right translates under the image of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$ span a finite-dimensional space, with, moreover, a single finite-dimensional space of functions on that subgroup containing all $k\mapsto \psi_e(s)(gk)$ uniformly in $s,g$; the stabiliser under right translation inside the kernel of the archimedean projection is open; right invariance under $\mathrm{principalLevel}(N)$ intersected with that kernel, for a nonzero ideal $N$; and, on each vertical strip $|\sigma'|\le\sigma_0$ and compact $C$, a bounded integrable majorant for $(1+|t|)^n\|\psi_e(\sigma'+it)(g)\|$. Let $M^c_e(s,g)$ be meromorphic in normal form on $\mathbb{C}$ in $s$ and equal to the Weyl intertwining integral $\int \psi_e(s)(w^{-1}u(x)g)\,dx$ against adelic additive Haar measure for $\operatorname{Re}s>1/2$. Fix $e$ and put, for $k$ in the maximal compact subgroup (integral finite part, row-isometric archimedean components) with its Haar measure, $a_e(t,k)=\psi_e(it)(k)$ and $b_e(t,k)=\operatorname{vol}(\mathrm{adelicBox})^{-1}\lim_{s\to -it}M^c_{re}(s,k)$, and $A_e(t)=\int a_e\overline{a_e}$, $B_e(t)=\int a_e\overline{b_e}$, $C_e(t)=\int b_e\overline{b_e}$. Then $A_e,B_e,C_e$ are integrable on $\mathbb{R}$, for every $t$ the functions $a_e(t,\cdot)\overline{b_e(t,\cdot)}$ and $b_e(t,\cdot)\overline{b_e(t,\cdot)}$ are integrable on the maximal compact subgroup, and $C_e(t)=A_{re}(-t)$ for all $t$.
--
--   This packages the analytic input — integrability of the three pairings along the unitary axis, and the reflection identity expressing unitarity of the intertwining operator on the axis — for the Paley–Wiener form of the Plancherel/Parseval identity for pseudo-Eisenstein series. It is used by [`AutomorphicForm.setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_normSq_add_weylIntertwining_of_principalLevel_slab`](thm.html#AutomorphicForm.setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_normSq_add_weylIntertwining_of_principalLevel_slab), whose remaining content is the algebraic expansion of $\|a+b\|^2$ and the reindexing by $e\mapsto re$, $t\mapsto -t$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open scoped ComplexConjugate

theorem AutomorphicForm.integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (ι : Type) [Fintype ι]
      (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ))
      (r : ι → ι) (_hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
      (_hdist : ∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite F (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth F (ψf e s))
      (_hψKu : ∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (N : Ideal (𝓞 F)) (_hN : N ≠ ⊥)
      (_hψlev : ∀ e (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ψf e s (g * u) = ψf e s g)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (Mc : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ (e : ι) (g : AdelicGL2 (𝓞 F) F), MeromorphicNFOn (fun s : ℂ => Mc e s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc e s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s) g)
      (e : ι),
    let a : ι → ℝ → adelicMaximalCompact F → ℂ :=
      fun e t k => ψf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
    let b : ι → ℝ → adelicMaximalCompact F → ℂ :=
      fun e t k => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
        Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F))
    let A : ι → ℝ → ℂ := fun e t => ∫ k, a e t k * conj (a e t k) ∂(maximalCompactHaar F)
    let B : ι → ℝ → ℂ := fun e t => ∫ k, a e t k * conj (b e t k) ∂(maximalCompactHaar F)
    let C : ι → ℝ → ℂ := fun e t => ∫ k, b e t k * conj (b e t k) ∂(maximalCompactHaar F)
    Integrable (A e) ∧ Integrable (B e) ∧ Integrable (C e) ∧
    (∀ t : ℝ, Integrable (fun k => a e t k * conj (b e t k)) (maximalCompactHaar F)) ∧
    (∀ t : ℝ, Integrable (fun k => b e t k * conj (b e t k)) (maximalCompactHaar F)) ∧
    (∀ t : ℝ, C e t = A (r e) (-t)) := by sorry
