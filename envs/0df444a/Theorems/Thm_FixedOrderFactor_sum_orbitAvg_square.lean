-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_orbitAvg_square
-- name    : FixedOrderFactor.sum_orbitAvg_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:08:05.009438+00:00
-- url     : https://prove2.me/theorems/1f6818c3-c832-402c-90a6-aa075993ec9f
-- title:
--   Fixed Order Factor: sum orbit Avg square
-- statement:
--   **The prime-square term.** For `M > 0` and `s ∣ M`, the squares `(t, y)² = ((1 + y)t, y²)` of the
--   elements of `ℤ/s ⋊ (ℤ/M)ˣ` lying over `a` give
--   `∑_{y ∈ (ℤ/M)ˣ, y² = a} ∑_{t<s} ϱ_s((ȳ + 1)t) = s · β(M, a, s)`, where `ȳ ∈ ℤ/s` is the image of `y`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L194-L198
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L194-L198

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sum_orbitAvg_square {M : ℕ} [NeZero M] {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : ZMod M => IsUnit y ∧ y ^ 2 = a),
      ∑ t ∈ Finset.range s, orbitAvg s (((ZMod.castHom hs (ZMod s) y).val + 1) * t) =
      s * sqrtCount M a s := by sorry
