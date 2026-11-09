-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_theorem_1_1
-- name    : BipartiteVRM.Competitive.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:44.845019+00:00
-- url     : https://prove2.me/theorems/171a405d-06ed-4e9d-9402-3a9533830b20
-- title:
--   Theorem 1.1 — full explicit VRM bound and deterministic online behavior
-- statement:
--   For every fixed real $\gamma>1$ and every fixed causal deterministic rule for all event and minimum-path ties, VRM is a deterministic online algorithm in any metric space. Its irrevocable output is a feasible perfect matching and it eventually completes on every finite balanced input. On each input with $m\ge1$, its actual distance-plus-both-sides-waiting cost satisfies
--
--   $$\mathrm{ALG}\le\left(2+\frac{2\gamma}{\gamma-1}\right)
--   \bigl[1+(\gamma+1)(1+\ln m)\bigr]\mathrm{OPT}.$$
--
--   The explicit specialization is also a conclusion:
--
--   $$\gamma=2\quad\Longrightarrow\quad
--   \mathrm{ALG}\le(24+18\ln m)\mathrm{OPT}.$$
--
--   For the empty input the output is empty and $\mathrm{ALG}=\mathrm{OPT}=0$. The offline benchmark is the attained minimum of the actual feasible timed objective, not a comparison scalar. Across different ambient metric spaces and different final input sizes, inputs with identical observations through $t$ give identical output through $t$; thus VRM needs neither the metric space nor $m$ in advance.
--
--   This is the complete headline theorem, including the algorithmic clauses. It retains arbitrary real times, simultaneous arrivals, coincident locations, $m=1$, and zero-optimum inputs. All execution and benchmark well-posedness properties are conclusions; no waiting bound, correctness invariant, or competitive ratio is assumed.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: the minimum actual distance-plus-both-sides-delay objective OPT in (2.1) → the real projection of its ENNReal infimum over every perfect matching and feasible real match-time function; reason: offline_attainment and the main goal conclude finiteness and attainment, so the projection never substitutes a default for an infinite value
--   - encoding: deterministic online algorithm needing neither the metric space nor m in advance → ExecutionCorrect and Causal, including comparison of inputs in different metric spaces and with different final sizes; reason: these express termination, feasible immutable perfect output, uniqueness and dependence solely on the observations permitted by §2.1
--   - generalization: the displayed logarithmic coefficient on nonempty inputs, where ln m is defined → the identical bound for m at least one, plus a separate empty-input branch with empty output and ALG = OPT = 0; reason: this extends only the undefined logarithmic boundary and preserves every nonempty input and the exact coefficient
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 2–3, Theorem 1.1; pp. 6–12, §2–§4; p. 25, Appendix A

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

universe uVRMgoal

namespace BipartiteVRM.Competitive

/-- Full Theorem 1.1, pp. 2–3. Causality compares different metric spaces and
different input sizes; completion and irrevocability are conclusions. The source's
logarithmic bound is stated for m≥1, with the empty input handled separately. -/
theorem theorem_1_1 (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) :
    Causal.{uVRMgoal, uVRMgoal} γ tie ∧
    ∀ {X : Type uVRMgoal} [MetricSpace X] (I : Input X),
      ExecutionCorrect I γ tie ∧ OfflineAttained I ∧
      (I.size = 0 → output I γ tie = [] ∧ ALG I γ tie = 0 ∧ OPT I = 0) ∧
      (0 < I.size → ALG I γ tie ≤
        (2 + 2 * γ / (γ - 1)) *
          (1 + (γ + 1) * (1 + Real.log (I.size : ℝ))) * OPT I) ∧
      (γ = 2 → 0 < I.size → ALG I γ tie ≤
        (24 + 18 * Real.log (I.size : ℝ)) * OPT I) := by sorry

end BipartiteVRM.Competitive
