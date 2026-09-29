-- Prove2me | Theorems.Thm_BanditAlgorithm_optimal_allocation_choice_tendsto
-- name    : BanditAlgorithm.optimal_allocation_choice_tendsto
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T05:25:05.110718+00:00
-- url     : https://prove2.me/theorems/dc083e6f-4817-41f6-901c-e9fa1c36cd50
-- title:
--   The plug-in optimal allocation is continuous at a unique best arm
-- statement:
--   Fix a rule $\mathrm{choice}$ assigning to every Gaussian parameter vector with a unique best arm a full-support optimal allocation. Then along any sequence of estimates $\hat\mu(s)\to\mu$, where $\mu$ has a strictly best arm,
--   $$\mathrm{choice}(\hat\mu(s))_j\ \longrightarrow\ \mathrm{choice}(\mu)_j\qquad\text{for every arm }j.$$
--
--   No continuity of the rule is assumed, and none could be: a rule is only required to *select* an optimal allocation, and a selection is in general discontinuous. The point is that here there is nothing to select. By uniqueness of the optimal allocation, the rule is pinned down at every parameter with a strictly best arm, so it coincides there with the canonical selection and inherits its regularity.
--
--   That regularity is the argmax half of Berge's maximum theorem at a point of unique maximisation: for a jointly continuous objective on a compact feasible set, every maximiser at a nearby parameter is near the unique maximiser at the limit. Continuity of the objective is needed only along the feasible set, which matters because the pair weight $\alpha_i\alpha_j/(\alpha_i+\alpha_j)$ is continuous on the closed simplex but not off it.
--
--   The statement is about a sequence rather than a neighbourhood because the estimates fed to the rule need not have a strictly best arm at every round --- only eventually, since having a strictly best arm is an open condition. The rule may return anything at parameters with ties, and the conclusion is unaffected.
--
--   This is the hypothesis a tracking sampling rule requires: the targets it follows converge, so its empirical allocation inherits the limit by a Ces\`aro argument.
-- source:
--   Continuity of the optimal-allocation map for Gaussian best-arm identification, from uniqueness (Garivier & Kaufmann, COLT 2016, Lemma 4) and Berge's maximum theorem; needed for the D-Tracking guarantee of Garivier & Kaufmann, Section 2.2 / Lattimore & Szepesvari, Algorithm 21, line 8.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Theorems.Thm_BanditAlgorithm_gaussian_optimal_allocation_unique
import Theorems.Thm_BanditAlgorithm_argmax_dist_le_of_unique_maximiser
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Lattice

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter Topology

theorem BanditAlgorithm.optimal_allocation_choice_tendsto {k : ℕ} [NeZero k]
    (choice : (Fin k → ℝ) → Fin k → NNReal)
    (hchoice : ∀ m : Fin k → ℝ, (∃ i : Fin k, ∀ j, j ≠ i → m j < m i) →
      (∀ i, 0 < choice m i) ∧
        BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit m)
          (Set.range (BanditAlgorithm.gaussianBandit (k := k))) (choice m))
    {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {m : ℕ → Fin k → ℝ} (hm : Filter.Tendsto m Filter.atTop (nhds μvec))
    (j : Fin k) :
    Filter.Tendsto (fun s ↦ ((choice (m s) j : ℝ))) Filter.atTop
      (nhds ((choice μvec j : ℝ))) := by
  sorry
