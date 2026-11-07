-- Prove2me | Theorems.Thm_CubicProductLB_eq_295
-- name    : CubicProductLB.eq_295
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:15.794455+00:00
-- url     : https://prove2.me/theorems/9d5933bb-9fee-4943-8d32-92a70a611a9b
-- title:
--   Eq. (295) — $b_M$ is not 2-simple for $M = 2^d$, also after adding a constant
-- statement:
--   Let $q > 3$ be the target prime. Combining Lemmas 16 and 17,
--   $$b_M \text{ is not 2-simple whenever } M = 2^d,$$
--   and the same remains true after adding a constant in $\mathbb F_2$, because a constant changes only the coefficient of the empty monomial.
--
--   Differences from the source:
--   - reading: the target modulus q, with its hypothesis stated where it is used (q ≠ 3 at (266), q odd prime at (292), and "Fix the target prime q > 3" at p.37) → q prime and q > 3 as hypotheses; reason: the sections share this one target prime
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (295) and the sentence after it, p.34

import Mathlib
import Definitions.Def_CubicProductLB_targetBit
import Definitions.Def_CubicProductLB_IsTwoSimple

namespace CubicProductLB

/-- Eq. (295) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (295) and the sentence after it, p.34). `b_M` is not 2-simple whenever
`M = 2^d`, and this remains true after adding a constant in `F_2`.

**Formalization Note** `q` is the target prime `q > 3`. -/
theorem eq_295 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) (d : ℕ) :
    ¬ IsTwoSimple (targetBit q (2 ^ d)) ∧
    ∀ δ : ZMod 2, ¬ IsTwoSimple (fun y => targetBit q (2 ^ d) y + δ) := by sorry

end CubicProductLB
