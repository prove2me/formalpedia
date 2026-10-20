-- Prove2me | Theorems.Thm_CompactnessConjecture_proposedFamilyFree_minDegree_polynomial_le
-- name    : CompactnessConjecture.proposedFamilyFree_minDegree_polynomial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/e091d282-20d9-42b8-bfe2-a206eecd2818
-- title:
--   CompactnessConjecture.proposedFamilyFree_minDegree_polynomial_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph

theorem CompactnessConjecture.proposedFamilyFree_minDegree_polynomial_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 ≤
      864 * (n : ℝ) ^ 5 := by sorry
