-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_lw_cf
-- name    : CompanionTheory.CapEig.lw_cf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:37:04.344055+00:00
-- url     : https://prove2.me/theorems/10945474-a276-5aba-b35d-99b56476250d
-- title:
--   Cap Eig: lw cf
-- statement:
--   The Cap Eig construction uses the lw cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefCC.lean#L41-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefCC.lean#L41-L64

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefCC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig
open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt CompanionTheory.LimBd.Main
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (B.Mat k r)} {σ : B.Mat k r → (H →L[ℂ] H)}

theorem CompanionTheory.CapEig.lw_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a : H}
    (ha : IsSm G σ a) (b : H) {f : B.Mat k r → E} (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {u : List (B.Mat k r)}, LieW G u → ∀ g ∈ G,
      u.foldr B.LdV f g = cf σ x₀ (dsW σ u a) b g
  := by sorry
