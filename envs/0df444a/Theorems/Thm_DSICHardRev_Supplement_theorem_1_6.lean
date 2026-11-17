-- Prove2me | Theorems.Thm_DSICHardRev_Supplement_theorem_1_6
-- name    : DSICHardRev.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:12:53.781768+00:00
-- url     : https://prove2.me/theorems/d63b299a-92a8-485b-a317-d4ce9638eaf8
-- title:
--   Theorem 1.6 — a simultaneous $(41-\sqrt6)/50\approx0.771$-approximation for two matroid rank valuations with polynomial communication
-- statement:
--   Consider two bidders with matroid rank valuations on $m$ items and (possibly randomized) simultaneous algorithms.
--
--   **Theorem.** There are constants $C$ and $k$ such that for every $m\ge1$ there is a simultaneous algorithm for two bidders on $m$ items that uses at most $C\,m^k$ bits of communication and satisfies, for every pair of matroid rank functions $v_1,v_2$,
--   $$
--   \mathbb E\big[v_1(S_1)+v_2(S_2)\big]\;\ge\;\frac{41-\sqrt6}{50}\,\max_{(T_1,T_2)}\big(v_1(T_1)+v_2(T_2)\big).
--   $$
--
--   Since $(41-\sqrt6)/50\approx0.771>3/4$, this beats the tight simultaneous $3/4$-approximation for binary XOS valuations; binary submodular valuations are exactly matroid rank functions.
--
--   **Formalization Note** "Polynomial communication" is read as $\le C m^k$ with $C,k$ independent of $m$. The constant is exact. The algorithm may use private randomness for each bidder and a randomized referee.
--
--   Differences from the source:
--
--   - reading: using polynomial communication → ∃ C : ℝ, ∃ k : ℕ, ∀ m ≥ 1: comm ≤ C · m^k; reason: standard reading with C and k uniform in m
--   - reading: simultaneous algorithm, each bidder sends a (possibly random) message → TwoSimAlg: private-coin message distributions per bidder and a randomized referee; reason: the paper's model (p.8, Definition 2.5); App. C samples bases privately and mixes two procedures
--   - encoding: communication = worst-case transcript length → ∑ i, ⌈log₂ K_i⌉ for alphabets Fin K_i; reason: the base mission's SimAlg.comm convention
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), Theorem 1.6, p.3 (proof App. C, pp.36–42)

import Mathlib
import Definitions.Def_DSICHardRev_Supplement_Domains
import Definitions.Def_DSICHardRev_Supplement_TwoSimAlg

namespace DSICHardRev

namespace Supplement

/-- **Theorem 1.6** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §1.2, p.3; proof App. C, pp.36–42):
there exists a `(41 − √6)/50 ≈ 0.771`-approximation for two matroid rank valuations with a
simultaneous algorithm using polynomial communication.

**Formalization Note.** "Polynomial communication" is read as: there are constants `C` and `k`,
independent of `m`, such that for every `m ≥ 1` there is a (possibly randomized) simultaneous
algorithm for two bidders on the items `Fin m` with at most `C · m^k` bits of communication and
`((41 − √6)/50) · OPT ≤ E[welfare]` on every pair of matroid rank functions on `Fin m`. The ratio
is the exact constant `(41 − √6)/50`. -/
theorem theorem_1_6 :
    ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ, 1 ≤ m → ∃ A : TwoSimAlg m,
      (A.comm : ℝ) ≤ C * (m : ℝ) ^ k ∧
      A.IsApproxRatio (DMR m) ((41 - Real.sqrt 6) / 50) := by sorry

end Supplement

end DSICHardRev
