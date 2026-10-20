-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_badSaturationRows_lt_pow
-- name    : ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_lt_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/d26a49d7-b54f-4e0d-b14f-5d4b89d6944d
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_lt_pow
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_lt_pow (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card < H ^ (H ^ m - 1) := by sorry
