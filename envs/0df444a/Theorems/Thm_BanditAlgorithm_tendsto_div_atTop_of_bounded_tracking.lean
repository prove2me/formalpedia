-- Prove2me | Theorems.Thm_BanditAlgorithm_tendsto_div_atTop_of_bounded_tracking
-- name    : BanditAlgorithm.tendsto_div_atTop_of_bounded_tracking
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:19:10.859802+00:00
-- url     : https://prove2.me/theorems/bd00b7c2-2322-40d8-b1a6-edbfab769daa
-- title:
--   Bounded tracking of a convergent target: $M(t)/t\to a$
-- statement:
--   Let $p(0),p(1),\dots$ be reals with $p(s)\to a$, and let $M(t)$ be a sequence staying within a fixed distance of the partial sums,
--   $$\left|M(t)-\sum_{s<t}p(s)\right|\le C\qquad\text{for all }t.$$
--   Then $M(t)/t\to a$.
--
--   This is the tracking half of Garivier & Kaufmann's Lemma 8, stripped of everything bandit-specific. A sampling rule maintains target allocations $p(s)$ — in Track-and-Stop, $p(s)=\alpha^*(\hat\mu(s))$, which converges once the empirical means do — and plays so that the realised count $N_i(t)$ stays within a constant of the cumulative target $\sum_{s<t}p_i(s)$. The conclusion $N_i(t)/t\to\alpha_i$ is then immediate: the Cesaro average of the targets converges to $a$, and the discrepancy contributes $C/t\to0$.
--
--   The two hypotheses are exactly the two halves of a tracking rule: convergence of the targets, which comes from convergence of the empirical means together with continuity of the allocation map, and the bounded discrepancy, which is what the greedy "play the arm furthest behind its target" step delivers.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Lemma 8 (the tracking half of D-Tracking), stated abstractly; the Cesaro step is Mathlib's Filter.Tendsto.cesaro.

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter Topology

theorem BanditAlgorithm.tendsto_div_atTop_of_bounded_tracking {p : ℕ → ℝ} {a C : ℝ}
    (hp : Filter.Tendsto p Filter.atTop (nhds a)) (M : ℕ → ℝ)
    (hbd : ∀ t : ℕ, |M t - ∑ s ∈ Finset.range t, p s| ≤ C) :
    Filter.Tendsto (fun t : ℕ ↦ M t / (t : ℝ)) Filter.atTop (nhds a) := by
  sorry
