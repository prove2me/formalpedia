-- Prove2me | Theorems.Thm_FirstPrice_efficiency
-- name    : FirstPrice.efficiency
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:46:10.380819+00:00
-- url     : https://prove2.me/theorems/b2b164c9-a952-4def-a8d7-94ade43d6e84
-- title:
--   Jin–Lu Theorem 1 — every first-price value-auction BNE is $(1-e^{-2})$-efficient
-- statement:
--   Consider a single-item first-price auction with finitely many bidders, independent private values, mixed strategies, and an arbitrary measurable highest-bid tie rule. Suppose all declared value sets lie in $[0,B]$ for a fixed real $B\ge0$, and the mixed profile is an exact Bayes–Nash equilibrium with nonnegative bids, no overbidding, and every nonnegative pure deviation tested. Then
--   $$
--   \mathbb E[W_{\mathrm{eq}}]\ge(1-e^{-2})\,\mathbb E[\max_i v_i].
--   $$
--   Here $W_{\mathrm{eq}}$ is the value of the selected bidder; expectations include private values, independent mixing, and randomized tie breaking. This is the sharp efficiency theorem of Jin and Lu. The nonnegative-extended-real formulation does not silently replace an unbounded welfare by zero; the common value bound makes both expectations finite.
--
--   This theorem is the shared upper-bound dependency for `ProcurementPoA.DeterministicCap.capped_margin_efficiency` and companion `Supplement.theorem_4_1`. The cap transformation uses values $(T-c_i)_+$; the bounded-bid transformation uses values $U-c_i$.
--
--   **Formalization Note** `FirstPrice.IsBNE` includes no overbidding, as in the value-auction instances obtained from no-underbidding procurement equilibria. The arbitrary `TieRule` is evaluated on negated bids, so no uniform- or deterministic-tie assumption is imposed.
-- source:
--   Y. Jin and P. Lu, First Price Auction is 1-1/e^2 Efficient, J. ACM 70(5), 2023, Theorem 1, https://doi.org/10.1145/3617902 and https://arxiv.org/abs/2207.01761; invoked by Palazzotto–Cristi, STOC 2027 submission 293, Theorem 4.1 proof p. 9 and Appendix A.1.1 p. 18.

import Mathlib
import Definitions.Def_FirstPrice_ValueAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open MeasureTheory ProbabilityTheory
open scoped Classical

theorem FirstPrice.efficiency {n : ℕ}
    (D : ProcurementPoA.DeterministicCap.IndependentTypes n)
    (τ : ProcurementPoA.DeterministicCap.TieRule n)
    (σ : ProcurementPoA.DeterministicCap.MixedProfile n)
    (B : ℝ) (hB : 0 ≤ B) (hval : ∀ i, D.types i ⊆ Set.Icc 0 B)
    (heq : IsBNE D τ σ) :
    ENNReal.ofReal (1 - ProcurementPoA.DeterministicCap.epsilon) * optimalWelfare D ≤
      welfare D τ σ := by sorry
