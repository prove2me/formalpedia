-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_mul_mem_spanBox_of_gap
-- name    : CompanionTheory.LimBd.Main.mul_mem_spanBox_of_gap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:44.740214+00:00
-- url     : https://prove2.me/theorems/aaba4fbb-1893-5e09-8916-cca30f85cddb
-- title:
--   Main: mul mem span Box of gap
-- statement:
--   The Main construction uses the mul mem span Box of gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L121-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/Letter.lean#L121-L156

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}

theorem CompanionTheory.LimBd.Main.mul_mem_spanBox_of_gap (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) (hZ : ZuckT t) (hZd : ZuckDualT t) (k r : ℕ)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (d : ℕ) (q φ : B.Mat k r → ℂ)
    (hq : q ∈ Letters k r ^ d) (hφ : IsCoef k r ε lam φ) (hg : PI.ZuckTensor.GapAtLeast ε lam h)
    (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) : q * φ ∈ SpanBox k r ε lam (d : ℝ) := by sorry
