-- Prove2me | Theorems.Thm_BellDetEff_TwoParty_eqs_13_14_witness
-- name    : BellDetEff.TwoParty.eqs_13_14_witness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:08.459997+00:00
-- url     : https://prove2.me/theorems/763da0a0-0a3b-407a-b1d7-e8ed4e2bfb26
-- title:
--   Eqs. (13)–(14) — the box p^NS(a, b|x, y) = 1/P [a + b ≡ xy mod P] is a no-signaling distribution
-- statement:
--   Let $P$ be a prime and $M_A,M_B$ natural numbers. Define, for $a,b\in\{0,\dots,P-1\}$, $x\in\{1,\dots,M_A\}$, $y\in\{1,\dots,M_B\}$,
--   $$p^{NS}(a,b\mid x,y)=\begin{cases}1/P & a+b\equiv xy \pmod P,\\ 0 & \text{otherwise.}\end{cases}$$
--   Then:
--   1. for every $(x,y)$, $p^{NS}(\cdot,\cdot\mid x,y)$ is a probability distribution;
--   2. $p^{NS}$ satisfies the no-signaling condition (1);
--   3. $\sum_b p^{NS}(a,b\mid x,y)=1/P$ for all $a,x,y$ (eq. (14)), and $\sum_a p^{NS}(a,b\mid x,y)=1/P$ for all $b,x,y$.
--
--   This box is the no-signaling behaviour whose Bell value under detector inefficiency gives the upper bound of Theorem 2.
--
--   **Formalization Note** Outputs are `Fin P` read in `ZMod P`, and the paper's inputs are `x.val + 1`, `y.val + 1`.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, p. 3, proof of Theorem 2, eqs. (13)–(14)

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_BellInequality

namespace BellDetEff.TwoParty

/-- Eqs. (13)–(14), proof of Theorem 2 (Cao–Peng, arXiv:1607.04350v1, p. 3): for a prime `P`, the
behaviour `p^NS(a, b|x, y) = 1/P` if `a + b ≡ xy (mod P)`, `0` otherwise, is a probability
distribution for every pair of inputs, is no-signaling, and has both marginals equal to `1/P`. -/
theorem eqs_13_14_witness (P MA MB : ℕ) [Fact P.Prime] :
    IsBehaviour (witnessBox P MA MB) ∧ NoSignaling (witnessBox P MA MB) ∧
      (∀ a x y, ∑ b, witnessBox P MA MB a b x y = 1 / (P : ℝ)) ∧
      (∀ b x y, ∑ a, witnessBox P MA MB a b x y = 1 / (P : ℝ)) := by sorry

end BellDetEff.TwoParty
