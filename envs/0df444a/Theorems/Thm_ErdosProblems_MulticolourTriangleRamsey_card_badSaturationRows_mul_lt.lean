-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_badSaturationRows_mul_lt
-- name    : ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_mul_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/2b7248b1-a4f7-4adc-bb48-cfce1bb7e693
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_mul_lt
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_mul_lt (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card * H < H ^ (H ^ m) := by sorry
