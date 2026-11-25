-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_rw_cf
-- name    : CompanionTheory.CapEig.rw_cf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:27:49.552802+00:00
-- url     : https://prove2.me/theorems/db01cd38-0f6f-5583-af19-f84e4d1bccf0
-- title:
--   Cap Eig: rw cf
-- statement:
--   The Cap Eig construction uses the rw cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefCC.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefCC.lean#L24-L39

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

theorem CompanionTheory.CapEig.rw_cf (h : RepOn G σ) (x₀ : E) (a : H) {b : H} (hb : IsSm G σ b) {f : B.Mat k r → E}
    (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {v : List (B.Mat k r)}, LieW G v → ∀ g ∈ G, B.Rw v f g = cf σ x₀ a (dsW σ v b) g
  := by sorry
