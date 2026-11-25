-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_prod_norm_le
-- name    : CompanionTheory.Bmu.prod_norm_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:43:26.577365+00:00
-- url     : https://prove2.me/theorems/9dfe12e1-0810-445b-83a0-f303bc662c75
-- title:
--   Bmu: prod norm le
-- statement:
--   The Bmu construction uses the prod norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ProdNormLe.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ProdNormLe.lean#L12-L21

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ProdNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem CompanionTheory.Bmu.prod_norm_le {n : ℕ} (W : List (Mat n)) {a : ℝ} (h : ∀ X ∈ W, ‖X‖ ≤ a) :
    (W.map fun X => ‖X‖).prod ≤ a ^ W.length := by sorry
