-- Prove2me | Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
-- name    : AutomorphicForm.axis_continuation_bruhatEisenstein_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/55293f87-f794-5ec9-b7c5-ecf0366886ae
-- title:
--   Archimedean type cut is preserved by the continued Eisenstein series
-- statement:
--   Let $F$ be a number field, let $\mathbb{A}$ be its adele ring and let $\alpha_m : \mathbb{A}^\times \to \mathbb{R}^\times$ be the unit-group homomorphism obtained from the distributive Haar character of $\mathbb{A}$ composed with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, the adele ring carrying its Borel $\sigma$-algebra. Assume $\alpha_m$ takes positive values, and let $\mu,\nu : \mathbb{A}^\times \to \mathbb{C}^\times$ be continuous characters of absolute value $1$ that are trivial on the image of $F^\times$. Let $\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$, written $\varphi_s$, be such that each $\varphi_s$ transforms under the Borel subgroup (lower-left entry zero) by the characters $\eta_1(s) = \mu \cdot \alpha_m^{s+1/2}$ on the $(0,0)$ entry and $\eta_2(s) = \nu \cdot \alpha_m^{-(s+1/2)}$ on the $(1,1)$ entry; each $\varphi_s$ has finite-dimensional span of right translates under the image in $\mathrm{GL}_2(\mathbb{A})$ of the row-isometry subgroup at every infinite place $w$, and an open stabiliser inside the kernel of the archimedean-component map; $\varphi$ is jointly continuous, holomorphic in $s$ for each $g$, and for each $w$ the functions $k \mapsto \varphi_s(gk)$ on the archimedean row-isometry subgroup all lie in one fixed finite-dimensional subspace independently of $s$ and $g$. Let $\mathrm{tys}$ be a family consisting, for each infinite place $w$, of finitely many finite-dimensional representations of the row-isometry group at $w$, and suppose every $\varphi_s$ lies in the associated cut $\bigsqcap_w \bigvee_i$ of type subspaces. Let $O \subseteq \mathbb{C}$ be open and preconnected, containing the line $\mathrm{Re}\,s = 0$ and the half-plane $\mathrm{Re}\,s > 1/2$, and let $E, N : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ be analytic on a neighbourhood of $O$ in $s$ for each $g$, jointly continuous on $O \times \mathrm{GL}_2(\mathbb{A})$, and satisfy, for $\mathrm{Re}\,s > 1/2$, $E(s)(g) = \varphi_s(g) + \sum_{\xi \in F} \varphi_s(w_0 u(\xi) g)$ with $w_0$ the adelic Weyl element and $u(\xi)$ the upper unipotent, and $N(s)(g) = \int_{\mathbb{A}} \varphi_s(w_0^{-1} u(x) g)\,dx$ for the adelic additive Haar measure. Then for every $s \in O$ the function $E(s)$ lies in the cut of $\mathrm{tys}$.
--
--   This is the statement that the archimedean $K$-type constraints imposed on the inducing sections persist through the analytic continuation of the Eisenstein series attached to them. It feeds the comparison of the continued Eisenstein series with its constant term and the level-type averaging arguments for the adelic $\mathrm{GL}_2$ spectral theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_mem_archCutSubmodule_of_forall_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_InducedSection
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
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.axis_continuation_bruhatEisenstein_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F] :
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
      (tys : ArchTypeFamily F) (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule F tys)
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
      (s : ℂ) (_hs : s ∈ Oφ),
    Eφ s ∈ archCutSubmodule F tys := by sorry
