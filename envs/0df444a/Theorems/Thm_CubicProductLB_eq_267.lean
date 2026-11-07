-- Prove2me | Theorems.Thm_CubicProductLB_eq_267
-- name    : CubicProductLB.eq_267
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:23.533149+00:00
-- url     : https://prove2.me/theorems/76f3b805-b2e0-4643-93ac-cc781a80fd00
-- title:
--   Eqs. (265)–(267) — the target under triple identification, $b_N \circ \iota_P = b_M$
-- statement:
--   Let $q > 3$ be the target prime, let $N = 3M$, and let $P$ be a triple partition of $[N]$. Then for every $y \in \{0,1\}^M$,
--   $$|\iota_P(y)| = 3|y|, \qquad q \mid 3|y| \iff q \mid |y|,$$
--   and therefore
--   $$b_N \circ \iota_P = b_M.$$
--   The identity holds for every triple partition, so clustering turns the $N$-variable target into the $M$-variable one.
--
--   Differences from the source:
--   - reading: the target modulus q, with its hypothesis stated where it is used (q ≠ 3 at (266), q odd prime at (292), and "Fix the target prime q > 3" at p.37) → q prime and q > 3 as hypotheses; reason: the sections share this one target prime
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eqs. (265)–(267), p.31

import Mathlib
import Definitions.Def_CubicProductLB_targetBit
import Definitions.Def_CubicProductLB_TriplePartition
import Definitions.Def_ShallowSym_weight

namespace CubicProductLB

/-- Eqs. (265)–(267) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eqs. (265)–(267), p.31). For a triple partition `P`:
`|ι_P(y)| = 3|y|`; `q ∣ 3|y| ⟺ q ∣ |y|`; and `b_N ∘ ι_P = b_M` with `N = 3M`.

**Formalization Note** `q` is the target prime `q > 3` standing in Sections 9–11. -/
theorem eq_267 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) (M : ℕ) (P : TriplePartition M) :
    (∀ y : Fin M → Bool, ShallowSym.weight (P.iota y) = 3 * ShallowSym.weight y) ∧
    (∀ y : Fin M → Bool, q ∣ 3 * ShallowSym.weight y ↔ q ∣ ShallowSym.weight y) ∧
    targetBit q (3 * M) ∘ P.iota = targetBit q M := by sorry

end CubicProductLB
