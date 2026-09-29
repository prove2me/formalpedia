-- Prove2me | Theorems.Thm_BanditAlgorithm_measurable_klucbIndex
-- name    : BanditAlgorithm.measurable_klucbIndex
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T02:42:25.735647+00:00
-- url     : https://prove2.me/theorems/3fe3b6cf-1a4a-4bab-af18-68a7b3acc2f0
-- title:
--   Measurability of the KL-UCB index
-- statement:
--   For every finite arm set, every history length, and every arm $i$, the KL-UCB index is a measurable real-valued function of the observed finite history:
--
--   $$
--   h\longmapsto U_i(h)
--   =
--   \sup\left\{q\in[0,1]:
--   d\!\left(\widehat\mu_i(h),q\right)
--   \le
--   \frac{\log f(n+1)}{T_i(h)}
--   \right\}.
--   $$
--
--   This measurability interface allows KL-UCB index events and their finite indicator sums to be integrated against canonical bandit measures.
--
--   **Formalization Note** The formal definition also includes explicit endpoint guards implementing the source’s infinite-divergence conventions at $q=0$ and $q=1$. This theorem is a purely formal bridge for the Algorithm 8 index definition.
-- source:
--   Purely formal measurability bridge for Lattimore and Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, Algorithm 8, printed p. 137; it concerns the platform definition klucbIndex implementing the displayed supremum and endpoint conventions.

import Definitions.Def_bernoulliRelativeEntropy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.measurable_klucbIndex
    {k n : ℕ} (i : Fin k) :
    Measurable (BanditAlgorithm.klucbIndex (n := n) i) := by
  sorry
