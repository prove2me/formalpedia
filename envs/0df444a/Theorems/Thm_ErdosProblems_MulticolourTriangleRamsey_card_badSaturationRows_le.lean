-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_card_badSaturationRows_le
-- name    : ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/6e264a8a-a22d-4519-a085-1b8b993b7676
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.card_badSaturationRows_le (H m : ℕ)
    (T : Finset (Fin m → Fin H)) :
    (badSaturationRows H m T).card ≤
      H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card)) := by sorry
