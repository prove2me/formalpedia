-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_cutoff_optimality
-- name    : CryptoMembership.PerfectInfo.cutoff_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:47.736875+00:00
-- url     : https://prove2.me/theorems/c8a72a29-7de6-476a-9a94-c63a80a137e7
-- title:
--   A.2, p. 32 (PDF 33) — optimal purchase sets are cutoff sets {A_i ≥ A*}; every equilibrium is a cutoff equilibrium
-- statement:
--   Assume the standing assumptions and fix $A$, $\xi$.
--
--   1. If $B$ is a measurable set of endowment exponents and $P>0$ is a price such that household optimality holds, i.e. for every $a$,
--   $$a\in B\iff P\le E[U_i\mid\mathcal I_i](a)\quad(\text{partners trade iff }A_j\in B),$$
--   then either $B=\emptyset$ or $B=[A^*,\infty)$ for some cutoff $A^*$.
--   2. Consequently every equilibrium purchase set has the form $B=[A^*,\infty)$.
--
--   No cutoff form is assumed: the purchase set ranges over all measurable sets. This is the optimality of the cutoff strategy in Proposition 2, part 1.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), A.2, p. 32 (PDF 33), paragraph after (11)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem cutoff_optimality (P : Params) (hP : P.Standing) (A xi : ℝ) :
    (∀ (B : Set ℝ) (price : ℝ), MeasurableSet B → 0 < price →
      (∀ a : ℝ, a ∈ B ↔ price ≤ expUtility P A B a) →
      B = ∅ ∨ ∃ a : ℝ, B = Set.Ici a) ∧
    (∀ (B : Set ℝ) (price : ℝ), IsEquilibrium P A xi B price → ∃ a : ℝ, B = Set.Ici a) := by sorry

end CryptoMembership.PerfectInfo
