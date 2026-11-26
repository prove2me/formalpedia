-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_orbitAvg_square_finite
-- name    : FixedOrderFactor.sum_orbitAvg_square_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:17.971429+00:00
-- url     : https://prove2.me/theorems/ccfd928e-42ad-583d-86cc-08c4ebac354d
-- title:
--   Fixed Order Factor: sum orbit Avg square finite
-- statement:
--   **The finite-sum identity**, over the representatives `0 ≤ x < M`, for all `M` and `s > 0`:
--   `∑_{x² ≡ a} ∑_{t<s} ϱ_s((x + 1)t) = s · β(M, a, s)`. It is vacuous at `M = 0`, and for `s ∤ M` it is
--   an identity of arithmetic counts that depend on the representatives, not a count of residue classes.
--   The group-theoretic reading is `sum_orbitAvg_square`, under `M > 0` and `s ∣ M`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L179-L182
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L179-L182

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sum_orbitAvg_square_finite {s : ℕ} (hs : 0 < s) (M a : ℕ) :
    ∑ x ∈ (Finset.range M).filter (fun x => Nat.Coprime x M ∧ x ^ 2 % M = a % M),
      ∑ t ∈ Finset.range s, orbitAvg s ((x + 1) * t) = s * sqrtCount M a s := by sorry
