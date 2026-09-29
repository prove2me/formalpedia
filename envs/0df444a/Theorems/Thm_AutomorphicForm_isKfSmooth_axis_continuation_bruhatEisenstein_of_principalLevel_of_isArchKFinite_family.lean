-- Prove2me | Theorems.Thm_AutomorphicForm_isKfSmooth_axis_continuation_bruhatEisenstein_of_principalLevel_of_isArchKFinite_family
-- name    : AutomorphicForm.isKfSmooth_axis_continuation_bruhatEisenstein_of_principalLevel_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/ed1709f8-31b4-5f30-82e2-8f01cb175ba7
-- title:
--   K_f-smoothness of the continued Eisenstein series
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}$ for its adele ring, and let $\alpha_m$ be the character of $\mathbb{A}^\times$ obtained from the module (distributive Haar) character valued in $\mathbb{R}_{\ge 0}$ pushed into $\mathbb{R}^\times$, assumed pointwise positive. Given two characters $\mu,\nu \colon \mathbb{A}^\times \to \mathbb{C}^\times$ that are unitary ($\lVert\chi(x)\rVert = 1$ for all $x$), trivial on the principal ideles $F^\times$, and continuous, and a family $\varphi_f \colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ such that for every $s$ the function $\varphi_f(s)$ transforms under the upper triangular subgroup by the characters $\mu\,\alpha_m^{s+1/2}$ and $\nu\,\alpha_m^{-(s+1/2)}$ applied to the two diagonal entries, is archimedean $K$-finite at every infinite place, is $K_f$-smooth, is jointly continuous in $(s,g)$, is holomorphic in $s$ for each $g$, and satisfies the uniform $K$-finiteness condition that at each infinite place $w$ a single finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ contains all the right-translate functions $k \mapsto \varphi_f(s)(gk)$. Let $N \neq 0$ be an ideal of $\mathcal{O}_F$ such that each $\varphi_f(s)$ is right invariant under the intersection of the principal level subgroup of $N$ with the subgroup of matrices having trivial archimedean component. Let $O_\varphi \subseteq \mathbb{C}$ and $E_\varphi, N_\varphi$ satisfy the package: $O_\varphi$ is open and preconnected and contains both the line $\Re s = 0$ and the half-plane $\Re s > 1/2$; for each $g$ the functions $s \mapsto E_\varphi(s)(g)$ and $s \mapsto N_\varphi(s)(g)$ are analytic on a neighbourhood of each point of $O_\varphi$; both are continuous on $O_\varphi \times \mathrm{GL}_2(\mathbb{A})$ jointly; for $\Re s > 1/2$ one has $E_\varphi(s)(g) = \varphi_f(s)(g) + \sum_{\xi \in F} \varphi_f(s)(w\, u(\xi)\, g)$ with $w$ the image of the Weyl element and $u(\xi)$ the upper unipotent matrix; and for $\Re s > 1/2$ the function $N_\varphi(s)$ is the Weyl intertwining integral $g \mapsto \int \varphi_f(s)(w^{-1} u(x) g)\,dx$ against adelic additive Haar measure. Then for every $s \in O_\varphi$ the function $E_\varphi(s)$ is $K_f$-smooth, that is, its stabiliser for right translation inside the subgroup of $\mathrm{GL}_2(\mathbb{A})$ with trivial archimedean component is an open subgroup.
--
--   This records that the analytically continued Bruhat–Eisenstein series attached to a holomorphic family of induced sections of principal level $N$ is smooth as a function on the finite adelic points, i.e. right invariant under an open subgroup of $\mathrm{GL}_2(\mathbb{A}_{F,f})$. It is one of the automorphy properties of $E_\varphi$ used in the comparison of the continued Eisenstein series with its constant term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isKfSmooth_axis_continuation_bruhatEisenstein_of_principalLevel_of_isArchKFinite_family.lean

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

theorem AutomorphicForm.isKfSmooth_axis_continuation_bruhatEisenstein_of_principalLevel_of_isArchKFinite_family
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
      (N : Ideal (𝓞 F))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, φf s (g * u) = φf s g)
      (_hN : N ≠ ⊥)
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
    IsKfSmooth F (Eφ s) := by sorry
