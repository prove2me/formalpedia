-- Prove2me | Theorems.Thm_CubicProductLB_lemma_17
-- name    : CubicProductLB.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:20:34.772081+00:00
-- url     : https://prove2.me/theorems/902a7d58-a326-4b14-aaa8-c14614d735f7
-- title:
--   Lemma 17 — full coefficient of the clustered MOD $q$ target
-- statement:
--   Let $q > 3$ be the target prime and let $M = 2^d$, where $d \ge 0$ is an integer. The coefficient of the full monomial $y_1 y_2 \cdots y_M$ in the unique multilinear polynomial over $\mathbb F_2$ representing $b_M$ is equal to $1$:
--   $$\widehat{b_M}([M]) = 1 \in \mathbb F_2.$$
--   This is the property of the target that the clustering cannot destroy.
--
--   Differences from the source:
--   - reading: the target modulus q, with its hypothesis stated where it is used (q ≠ 3 at (266), q odd prime at (292), and "Fix the target prime q > 3" at p.37) → q prime and q > 3 as hypotheses; reason: the sections share this one target prime
--   - encoding: the coefficient in the unique multilinear polynomial → every coefficient family c representing b_M has c(univ) = 1; reason: the representative exists and is unique (∃! proved in the sanity file), so the two say the same
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 17, Eqs. (268)–(269), p.32

import Mathlib
import Definitions.Def_CubicProductLB_targetBit
import Definitions.Def_CubicProductLB_IsMultilinearRep

namespace CubicProductLB

/-- Lemma 17 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 17, Eq. (269), p.32). For `M = 2^d`, `d ≥ 0`, the coefficient of the full
monomial in the unique multilinear polynomial over `F_2` representing `b_M` is `1`.

**Formalization Note** `q` is the target prime `q > 3`. `d = 0` (`M = 1`) is included. -/
theorem lemma_17 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) (d : ℕ)
    (c : Finset (Fin (2 ^ d)) → ZMod 2) (hc : IsMultilinearRep (targetBit q (2 ^ d)) c) :
    c Finset.univ = 1 := by sorry

end CubicProductLB
