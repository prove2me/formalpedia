-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_theorem_1_1_metric_gap
-- name    : BootstrapRecolorVerify.MetricGap.theorem_1_1_metric_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:06.031884+00:00
-- url     : https://prove2.me/theorems/c4b7ddfe-a012-4ab4-8983-8b7d1514da1f
-- title:
--   Theorem 1.1 / 6.1 — Nearly logarithmic metric LP gap
-- statement:
--   There are an absolute real constant $c>0$ and an integer $k_0\ge3$ such that for every integer $k\ge k_0$ there is a valid finite 0-extension instance $I$ with exactly $k$ terminals and positive metric relaxation value satisfying
--
--   $$\frac{\mathrm{OPT}(I)}{\mathrm{MetricLP}(I)}\ge c\,\frac{\log k}{(\log\log k)^5}.$$
--
--   The weights are nonnegative, the terminal distance is a metric, assignments are genuine terminal-fixing retractions, and the LP ranges over all pseudometric extensions of that terminal metric. The constants precede all instance data. The statement covers every sufficiently large terminal count, including the counts obtained by the source's zero-weight terminal padding. It imposes no hierarchical-construction, expansion, sampling, or cost-lower-bound hypothesis on the existential instance. This is the paper's full headline assertion.
--
--   **Formalization Note** The finite vertex set is reindexed as Fin N. Parallel objective edges are merged by summing weights after terminal distances have been computed. The LP value is an infimum, equal to the finite LP minimum on a valid instance with terminals.
--
--   Differences from the source:
--   - encoding: Ω(log k/(log log k)⁵) for every sufficiently large terminal count → absolute c>0 and k₀≥3 before every k and all instance data; reason: this is the full quantifier meaning of Theorem 6.1; the threshold can be enlarged to make the logarithms positive
--   - encoding: an arbitrary finite undirected instance, allowing parallel edges → a generic published instance on Fin N with parallel objective weights summed; reason: finite reindexing and merging preserve all retraction costs and all metric LP objectives
--   - encoding: the metric LP minimum → the infimum of the same feasible objectives with an explicit positive value; reason: the finite feasible LP is nonempty and bounded below and attains its optimum; positivity prevents division by zero
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Theorem 1.1 p.3, equivalently Theorem 6.1 p.19; padding §6.5 p.28, p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=3; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_MetricLP

namespace BootstrapRecolorVerify.MetricGap

/-- Makarychev, STOC 2027 submission #1436 (October 2026), Theorem 1.1 p.3,
equivalently Theorem 6.1 p.19. The constants precede all instance data;
every sufficiently large terminal count occurs, including padded counts. -/
theorem theorem_1_1_metric_gap :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∃ (N : ℕ) (I : ZeroExtensionGap.Instance (Fin N)),
        I.IsValid ∧ I.T.card = k ∧ 0 < MetricLP I ∧
        c * (Real.log k / (Real.log (Real.log k)) ^ 5) ≤ I.OPT / MetricLP I := by sorry

end BootstrapRecolorVerify.MetricGap
