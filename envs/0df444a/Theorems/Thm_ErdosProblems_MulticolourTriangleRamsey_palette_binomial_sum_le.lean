-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_palette_binomial_sum_le
-- name    : ErdosProblems.MulticolourTriangleRamsey.palette_binomial_sum_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/c18cdaef-031d-4bef-b3b5-067da5fd980f
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.palette_binomial_sum_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.palette_binomial_sum_le (N t s : ℕ)
    (hhalf : 2 * s ≤ t) (htN : t ≤ N) :
    (∑ d ∈ Finset.range s,
      t.choose d * (N - t).choose d) ≤
        s * t.choose s * N.choose s := by sorry
