-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/3b047f45-f79e-5d70-8078-f2c8c4e3e5bf
-- title:
--   Rapid decay of the truncated Eisenstein series on Φ₀
-- statement:
--   Let $F$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi_F$ be a set of elements of $\mathrm{GL}_2$ of the adele ring of $F$. Write $\alpha_m$ for the character of the idele group obtained from the distributive Haar character of the adele ring, taken with values in $\mathbb{R}^\times$, and assume $\alpha_m$ is everywhere positive. Let $\mu,\nu$ be characters of the ideles into $\mathbb{C}^\times$ that are unitary ($|\chi(x)|=1$ for all $x$), trivial on the principal ideles coming from $F^\times$, and continuous. Let $\varphi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that for every $s$ the function $\varphi_s$ transforms under the Borel subgroup by $\varphi_s(bg)=\eta_1(a(b))\,\eta_2(d(b))\,\varphi_s(g)$ with $\eta_1=\mu\cdot\alpha_m^{\,s+1/2}$ and $\eta_2=\nu\cdot\alpha_m^{-(s+1/2)}$ ($a(b),d(b)$ the diagonal entries), is finite under right translation by the row-isometry subgroup at each infinite place, has open stabiliser inside the kernel of the archimedean projection, is jointly continuous in $(s,g)$ and holomorphic in $s$ for each $g$, and additionally is archimedean-finite uniformly: for each infinite place $w$ a single finite-dimensional space of functions on that row-isometry subgroup contains all $k\mapsto\varphi_s(gk)$. Let $O$ be an open preconnected subset of $\mathbb{C}$ containing the imaginary axis and the half-plane $\operatorname{Re}s>1/2$, and let $E,N:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be analytic in $s$ on a neighbourhood of $O$ for each $g$, jointly continuous on $O\times\mathrm{GL}_2(\mathbb{A}_F)$, and satisfy, for $\operatorname{Re}s>1/2$, $E_s(g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s(w\,u(\xi)\,g)$ and $N_s(g)=\int\varphi_s(w^{-1}u(x)g)\,dx$ against additive Haar measure on the adeles, where $w$ is the image of the Weyl element and $u$ the upper unipotent. Then for every $s\in O$ and every $N_0\in\mathbb{N}$ there is $M\in\mathbb{R}$ such that for all $R\in\mathbb{R}$ and all $g$ in the canonical truncation domain attached to $(\alpha,\beta)$ with $e^{R}<H(g)$, where $H$ is the adelic height, one has $\|(\Lambda^{e^R}E_s)(g)\|\le M\,H(g)^{-N_0}$; here $\Lambda^{T}\phi=\phi-\mathbf 1_{\{H>T\}}\cdot\int\phi(u(x)\,\cdot)$, the integration being against the component of the production pins that is the conditional measure of adelic additive Haar measure given the adelic box, on the Borel $\sigma$-algebra of the adele ring.
--
--   This is the statement that the truncated continuation of the $\mathrm{GL}_2$ Eisenstein series decays faster than any power of the adelic height on the canonical truncation domain, with a bound independent of the cut-off parameter $R$. It is the form in which rapid decay enters the integrability and inner-product arguments for truncated Eisenstein series, and is cited in the proofs of square-integrability of $\Lambda^T E_s$ against the truncation domain, of the corresponding estimate for a sum of induced sections, and of the vanishing criterion for constant terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (s : ℂ), s ∈ Oφ → ∀ N : ℕ, ∃ M : ℝ, ∀ (R : ℝ) (g : AdelicGL2 (𝓞 F) F),
        g ∈ AutomorphicForm.canonicalTruncationDomain F α β → Real.exp R < NumberField.AdelicHeight.adelicHeight F g →
        ‖(@AutomorphicForm.lambdaT _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R) (Eφ s)) g‖ ≤
          M * (NumberField.AdelicHeight.adelicHeight F g) ^ (-(N : ℝ)) := by sorry
