-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/e344b626-ffd0-53f2-b6ba-684a2afebe6a
-- title:
--   Moderate growth of the continued Eisenstein constant term
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha<\beta$, and let $\Phi_F$ be a set of $\mathrm{GL}_2$ adelic points. Write $\alpha_m$ for the real-valued character of the idele group obtained from the module character `distribHaarChar` of the adele ring, assumed positive, and let $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be characters that are unitary (absolute value $1$ at every idele), trivial on the principal ideles $F^\times$, and continuous. Let $\varphi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that each $\varphi_s$ transforms under the adelic Borel subgroup by $\mu\,\alpha_m^{s+1/2}$ on the first diagonal entry and $\nu\,\alpha_m^{-(s+1/2)}$ on the second, is finite under right translation by the row-isometry subgroup at every infinite place, has open stabiliser under right translation by the kernel of the archimedean projection, with $\varphi$ jointly continuous, holomorphic in $s$ for each $g$, and with the archimedean translates at each infinite place lying in one finite-dimensional space of functions uniformly in $s$ and $g$. Let $O\subseteq\mathbb{C}$ and $E,N:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: $O$ is open, preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; $s\mapsto E_s g$ and $s\mapsto N_s g$ are analytic on a neighbourhood of each point of $O$; both are continuous on $O\times\mathrm{GL}_2(\mathbb{A}_F)$; and for $\mathrm{Re}\,s>1/2$ one has $E_s g=\varphi_s g+\sum_{\xi\in F}\varphi_s(w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u$ the upper unipotent embedding, and $N_s g=\int\varphi_s(w^{-1}u(x)g)\,dx$ against adelic additive Haar measure. Then for every $s\in O$ there exist reals $M,A$ such that for all $g$ in the canonical truncation domain attached to $(\alpha,\beta)$, $$\Big\|\int E_s(u(q)g)\,d\nu_0(q)\Big\|\le M\cdot H(g)^A,$$ where $H$ is the adelic height and $\nu_0$ is the measure recorded in the production carrier pins built from $\Phi_F$, the levels $M\mapsto \mathrm{principalLevel}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box, namely adelic additive Haar measure conditioned to the adelic box, taken on the Borel $\sigma$-algebra of $\mathbb{A}_F$.
--
--   This is the statement that the constant term along the unipotent radical of the analytically continued $\mathrm{GL}_2$ Eisenstein family is of moderate growth, measured in the adelic height, uniformly over the canonical truncation domain of the slab $\alpha<\beta$, with constants depending on the chosen point $s$. It feeds the integrability of the continued family against the truncation weight and the argument deducing vanishing of the continued Eisenstein series from vanishing of its constant term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain.lean

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

theorem AutomorphicForm.exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
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
      (s : ℂ), s ∈ Oφ → ∃ (M A : ℝ), ∀ (g : AdelicGL2 (𝓞 F) F),
        g ∈ AutomorphicForm.canonicalTruncationDomain F α β →
        ‖@AutomorphicForm.constantTerm _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) g‖ ≤
          M * (NumberField.AdelicHeight.adelicHeight F g) ^ A := by sorry
