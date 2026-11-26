-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_char_pow_eq_one
-- name    : FixedOrderFactor.sum_char_pow_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:38.845712+00:00
-- url     : https://prove2.me/theorems/e0126c9b-27fb-4ccc-a194-0eb154b562ef
-- title:
--   Fixed Order Factor: sum char pow eq one
-- statement:
--   **Orthogonality for characters of order dividing `r`.** For a prime `p` with `r ∣ p - 1`,
--   the sum of `χ(a) conj χ(b)` over the characters `χ` modulo `p` with `χʳ = 1` is `r` when
--   `a/b` is a nonzero `r`-th power modulo `p`, and `0` otherwise.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L119-L124
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L119-L124

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
open Classical

theorem FixedOrderFactor.sum_char_pow_eq_one (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : r ∣ p - 1) (a b : ZMod p)
    (hb : b ≠ 0) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ a * starRingEnd ℂ (χ b) =
      if ∃ c : ZMod p, c ≠ 0 ∧ a = c ^ r * b then (r : ℂ) else 0 := by sorry
