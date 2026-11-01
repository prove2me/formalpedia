-- Prove2me | Theorems.Thm_BayesClock_theorem_1
-- name    : BayesClock.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:05.415992+00:00
-- url     : https://prove2.me/theorems/b80b02d4-7aac-4700-89d1-b7e31d73f740
-- title:
--   Theorem 1: a deterministic single-price clock auction is an $O(\log\log k)$-approximation to the expected optimal welfare
-- statement:
--   There is an absolute constant $C>0$ such that for every finite set of bidders $N$, every downward-closed constraint $\mathcal F$ with $k$ maximal sets, and all independent value distributions $(D_i)_{i\in N}$, there is a deterministic single-price clock auction whose expected welfare $\mathrm{auc}$ satisfies
--
--   $$\mathrm{OPT}=\mathbb E_{v\sim D}\Big[\max_{F\in\mathcal F}\sum_{i\in F}v_i\Big]\le C\cdot\max\{1,\log\log k\}\cdot\mathrm{auc}.$$
--
--   The auction is chosen with knowledge of the distributions, but its prices do not depend on the realized values and its selection depends only on who accepted. Without prior information no deterministic clock auction attains any bounded factor, even for $k=2$.
--
--   Differences from the source:
--   - reading: O(log log k) → C · max(1, log log k) for every k ≥ 1, with C absolute and chosen before the instance; reason: log log k is 0 at k = 1 and negative at k = 2, where the paper still claims a bounded factor, so this is the strongest reading of the bound
--   - encoding: log log k in base 2 → Real.log (Real.log k) (natural); reason: for k ≥ 2, log₂ log₂ k = (ln ln k − ln ln 2)/ln 2, so max(1, log₂ log₂ k) ≤ 2 max(1, ln ln k) and max(1, ln ln k) ≤ max(1, log₂ log₂ k); C is existential, so no instance changes
--   - encoding: a downward-closed constraint → IsDownwardClosed 𝓕, including ∅ ∈ 𝓕; reason: it excludes only the empty family, which admits no auction
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Theorem 1, p.7

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_SinglePriceAuction
import Definitions.Def_BayesClock_OPT

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- Theorem 1, Feldman et al., *Bayesian and Randomized Clock Auctions*, arXiv:2202.09291v1, p.7:
"Every downward-closed setting with k maximal sets admits a deterministic single-price clock auction
that obtains an O(log log k) approximation to the expected optimal welfare if the full distribution D
is known."

**Formalization Note** The constant `C` is absolute: it comes before the bidders, the constraint and
the laws. The auction comes after the laws, because it may use `D`. `O(log log k)` is read as
`C · max 1 (log log k)` for every `k ≥ 1`, since `log log k` is `0` at `k = 1` and negative at `k = 2`,
where the claim is still meant (`Real.log`). Values lie in `ℝ≥0`, the laws `ν i` are arbitrary
probability measures, with atoms and with infinite means allowed, and all expectations are `ℝ≥0∞`-valued
lower integrals. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : Type*) [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N)),
        IsDownwardClosed 𝓕 →
        ∀ (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)],
          ∃ a : SinglePriceAuction 𝓕,
            OPT 𝓕 ν ≤
              ENNReal.ofReal
                  (C * max 1 (Real.log (Real.log (maximalSets 𝓕).card))) *
                a.expectedWelfare ν := by sorry

end BayesClock
