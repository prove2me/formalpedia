-- Prove2me | Theorems.Thm_ComplementFreeCA_ValueQuery_cf_le_card_mul_max_singleton
-- name    : ComplementFreeCA.ValueQuery.cf_le_card_mul_max_singleton
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:56:27.907502+00:00
-- url     : https://prove2.me/theorems/32bbbb22-8ee4-4845-943e-9a9649d18b61
-- title:
--   Proof of Theorem 5.1 — a CF valuation is at most |T| times its best single item
-- statement:
--   Let $v$ be a normalized, monotone, complement-free valuation on bundles of $M=\{1,\dots,m\}$, let $T\subseteq M$ and let $c\in T$ be an item maximizing $v(\{j\})$ over $j\in T$. Then
--   $$v(T)\;\le\;\sum_{j\in T} v(\{j\})\;\le\;|T|\cdot v(\{c\}).$$
--
--   This is the step "$v_i(\{c_i\})\ge v_i(T_i)/|T_i|$" of the second case of the proof of Theorem 5.1: a subadditive bidder's value for a small bundle is recovered, up to the bundle's size, by its most valuable single item.
--
--   **Formalization Note** The division by $|T|$ of the paper is avoided by stating the multiplied form; $c\in T$ makes $T$ nonempty.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 12, proof of Theorem 5.1, second case, parenthetical 'this is because of the CF property …'

import Mathlib
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic

open Finset

namespace ComplementFreeCA.ValueQuery

/-- Proof of Theorem 5.1 (p. 12): for a CF valuation and an item `c` of `T` maximizing
`v({j})` over `j ∈ T`, `|T| · v({c}) ≥ ∑_{j ∈ T} v({j}) ≥ v(T)`. -/
theorem cf_le_card_mul_max_singleton {m : ℕ} (v : Finset (Fin m) → ℝ) (hv : IsCFValuation v)
    (T : Finset (Fin m)) (c : Fin m) (hc : c ∈ T) (hmax : ∀ j ∈ T, v {j} ≤ v {c}) :
    v T ≤ ∑ j ∈ T, v {j} ∧ ∑ j ∈ T, v {j} ≤ (T.card : ℝ) * v {c} := by sorry

end ComplementFreeCA.ValueQuery
