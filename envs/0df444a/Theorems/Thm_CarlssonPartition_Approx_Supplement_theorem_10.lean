-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_10
-- name    : CarlssonPartition.Approx.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:35:55.657797+00:00
-- url     : https://prove2.me/theorems/bc44dff9-8bcb-4991-997b-13d8c07a0bc8
-- title:
--   Theorem 10 — convex approximately equitable partition with its uniform integration-oracle bound
-- statement:
--   There is a deterministic adaptive exact-integration algorithm and absolute constants $C>0$ and $\varepsilon_0>0$ with the following property. Let $R\subseteq\mathbb R^2$ be compact and convex with diameter one; let $m\ge1$ be an integer. The unknown probability measures $\mu_1,\mu_2$ have measurable nonnegative densities on $R$ with finite positive line-mass supremum $K$ as defined in §4. The algorithm is given only $R,m,K,\varepsilon$, for any $\varepsilon>0$, and learns the measures only through exact mass queries of convex regions.
--
--   It terminates with $m$ convex districts forming a partition of $R$ up to shared null boundaries, with
--   $$
--   \left|\mu_j(R_i)-\frac1m\mu_j(R)\right|\le\varepsilon
--   \quad(i=1,\ldots,m;\ j=1,2).
--   $$
--   For $0<\varepsilon<\varepsilon_0$ and $\varepsilon<Km/2$, the actual number of calls in this same terminating interaction satisfies
--   $$
--   N\le C\,\frac{K^2m^3}{\varepsilon^2}\log\frac{Km}{\varepsilon}.
--   $$
--   The algorithm and both constants are uniform over the unknown measures, region, fleet size and line-mass parameter. No numerical big-O constant is invented. Accuracy and termination are stated for every positive tolerance; the small-tolerance conditions apply only to the asymptotic query bound. This result supplies both the partition and the complete oracle-call guarantee rather than bare existence with an unrelated declared cost.
--
--   Differences from the source:
--   - reading: Theorem 10 uses O(K^2*m^3/epsilon^2 * log(K*m/epsilon)) exact mass calculations, with K and epsilon as above. → One algorithm and absolute positive C and epsilon0 precede all R,m,K,epsilon and unknown densities; the call estimate holds for epsilon<epsilon0 and epsilon<K*m/2, while correctness and termination hold for every epsilon>0.; reason: This quantifies a uniform big-O constant and a sufficiently small relative tolerance, keeping the logarithm positive without fixing a numerical constant. PDF 16 defines finite K and diameter normalization; PDF 19 and 22 specify exact integration; PDF 49 gives epsilon/m scaling.
--   - encoding: Two probability measures supported on R with K defined by line integrals of their densities; calls to their integration oracles. → The measures are constructed by restricted nonnegative density integrals, K is their exact extended line-mass supremum made finite, and a history-based query program returns both its partition and its derived call count.; reason: This retains all densities with finite source K, including unbounded measurable ones, and no polygonal or uniform density restriction. Queries are convex Borel regions, as every region the §4 procedure measures is convex; non-oracle exact geometric computations are not charged. Unknown densities are never arguments to the algorithm.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 20 (PDF 21), Theorem 10; §4 p. 15 (PDF 16); Remark 2 p. 21 (PDF 22); proof p. ec12 (PDF 49)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_PartitionOracle

namespace CarlssonPartition.Approx.Supplement

open CarlssonPartition.Equitable (Plane)
open scoped ENNReal

/-- Theorem 10, including both output accuracy and the uniform exact-integration
oracle bound. One algorithm family and one absolute constant work before either
unknown measure is supplied. The symbolic tolerance threshold is uniform as well;
epsilon < K*m/2 merely keeps the logarithmic asymptotic expression positive.
The algorithm must also terminate with correct output for every positive epsilon:
the small-tolerance restriction applies only to the complexity estimate. -/
theorem theorem_10 :
    ∃ (algorithm : PartitionAlgorithm) (C epsilon0 : ℝ),
      0 < C ∧ 0 < epsilon0 ∧
      ∀ (R : Set Plane), IsCompact R → Convex ℝ R → Metric.diam R = 1 →
      ∀ (m : ℕ), 1 ≤ m → ∀ (K epsilon : ℝ), 0 < K → 0 < epsilon →
      ∀ (g : Fin 2 → Plane → ℝ≥0∞), PartitionOracleInput R g K →
      ∃ (Rs : Fin m → Set Plane) (calls : ℕ),
        (algorithm R m K epsilon).Runs (massOracle R g) [] Rs calls ∧
        ConvexApproxPartition R g epsilon Rs ∧
        (epsilon < epsilon0 → epsilon < K * (m : ℝ) / 2 →
          (calls : ℝ) ≤ C * partitionQueryScale K m epsilon) := by sorry

end CarlssonPartition.Approx.Supplement
