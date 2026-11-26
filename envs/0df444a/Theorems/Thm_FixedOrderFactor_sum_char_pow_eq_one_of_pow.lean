-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_char_pow_eq_one_of_pow
-- name    : FixedOrderFactor.sum_char_pow_eq_one_of_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:28.594806+00:00
-- url     : https://prove2.me/theorems/9ac2d65d-884e-4add-9c4a-deee0863572e
-- title:
--   Fixed Order Factor: sum char pow eq one of pow
-- statement:
--   If `m = d aʳ` and `n = d bʳ` and `p ∤ m n`, every character of order dividing `r` modulo `p`
--   has `χ(m) conj χ(n) = 1`, so these pairs survive the average over the family.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L135-L139
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L135-L139

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

theorem FixedOrderFactor.sum_char_pow_eq_one_of_pow (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : r ∣ p - 1)
    {m n d a b : ℕ} (hm : m = d * a ^ r) (hn : n = d * b ^ r) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ m * starRingEnd ℂ (χ n) = r := by sorry
