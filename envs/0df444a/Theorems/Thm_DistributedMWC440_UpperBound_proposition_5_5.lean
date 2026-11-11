-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_proposition_5_5
-- name    : DistributedMWC440.UpperBound.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:19.069119+00:00
-- url     : https://prove2.me/theorems/13c14a18-a19e-4ffb-b9f0-ecf3396ac43e
-- title:
--   Proposition 5.5 (Approximation ratio and success probability)
-- statement:
--   Let $C^\star$ be a minimum cycle. The constants bounding $\epsilon\log n$ and the scale slack are fixed before the graph. Both scale inequalities are hypotheses. The conclusion is uniform over all positive scales and tree-like approximate SSSP outputs satisfying them.
--
--   Use all vertices as centers, real $k\ge1/2$, positive $d,\epsilon$, and
--
--   $$
--   \epsilon\in O(1/\log n),\qquad
--   2d(1-O(1/\log n))\le\mathrm{OPT}\le2(d-2\epsilon\delta_{\max}).
--   $$
--
--   One run finds a genuine cycle with weight estimate at most
--
--   $$
--   (k+1)(1+O(1/\log n))\mathrm{OPT}
--   $$
--
--   with probability $\Omega(n^{-1/k})$. The positive constants bounding the two hypothesis terms are arbitrary fixed constants; the approximation and probability constants and the size threshold are chosen uniformly before the graph, parameters, optimum cycle and output selection.
--
--   Differences from the source:
--   - generalization: positive polynomially bounded integer input lengths → arbitrary positive real lengths on the same finite connected undirected graph; reason: the stated analytic arguments use weighted path lengths and positivity only; every source input specializes to this setting
--   - encoding: asymptotic O, Omega and high-probability notation → positive constants and a size threshold quantified before the network and varying algorithm parameters; reason: this spells out the uniform asymptotic statement, retaining arbitrary real parameters and fixed polynomial confidence
--   - generalization: outputs of the specified approximate SSSP algorithm → any selection of the specified distance and parent-tree outputs, with the measure evaluated on the resulting event; reason: the lower-bound argument holds for every permitted tree choice, including the source algorithm; intended computable selections give ordinary measurable probability events
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Proposition 5.5, printed p. 26 / PDF p. 28.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem proposition_5_5 (epsilonBound scaleSlack : ℝ)
    (he : 0 < epsilonBound) (ha : 0 < scaleSlack) :
    ∃ (n₀ : ℕ) (C c : ℝ), 0 < C ∧ 0 < c ∧
    ∀ n ≥ max 3 n₀, ∀ (W : WGraph (Fin n)), W.graph.Connected →
      (∀ u v, W.graph.Adj u v → 0 < W.length u v) →
    ∀ (Cstar : Cycle W), IsMinimum Cstar → ∀ (k d ε : ℝ),
      1/2 ≤ k → 0 < d → 0 < ε → ε ≤ epsilonBound / Real.log n →
      2*d*(1-scaleSlack / Real.log n) ≤ Cstar.weight →
      Cstar.weight ≤ 2*(d-2*ε*deltaMax (Finset.univ : Finset (Fin n)) k d) →
    ∀ run : (δ : Shifts (Finset.univ : Finset (Fin n))) →
      LDDTree W Finset.univ k d ε δ,
      ENNReal.ofReal (c*(n : ℝ)^(-1/k)) ≤
        shiftLaw Finset.univ (rate (Finset.univ : Finset (Fin n)) k d)
          {δ | BasicSuccess (run δ) ((k+1)*(1+C / Real.log n)*Cstar.weight)} := by sorry

end DistributedMWC440.UpperBound
