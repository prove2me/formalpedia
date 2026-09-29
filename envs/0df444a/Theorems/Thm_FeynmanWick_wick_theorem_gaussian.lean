-- Prove2me | Theorems.Thm_FeynmanWick_wick_theorem_gaussian
-- name    : FeynmanWick.wick_theorem_gaussian
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:06:24.02605+00:00
-- url     : https://prove2.me/theorems/862efd33-4d37-4ada-b577-775d4e189fd1
-- title:
--   Wick's theorem: $\langle \phi_{k_1}\cdots\phi_{k_{2n}}\rangle$ is the sum over pairings
-- statement:
--   **Wick's theorem (Isserlis' theorem).** Let $\mu$ be a Gaussian probability measure on
--   $\mathbb{R}^d$ whose coordinate means all vanish, $\int x_i \, d\mu = 0$ for every
--   $i \in \{1,\dots,d\}$, and let $k_1, \dots, k_{2n}$ be any coordinate labels, not necessarily
--   distinct. Then the $2n$-point correlation function is the sum, over all pairings $\sigma$ of the
--   $2n$ positions, of the product of the two-point functions of the paired positions:
--
--   $$ \int \prod_{j=1}^{2n} x_{k_j} \, d\mu(x) \;=\; \sum_{\sigma \in P_n} \; \prod_{i \,:\, i < \sigma(i)} \left( \int x_{k_i} x_{k_{\sigma(i)}} \, d\mu(x) \right). $$
--
--   Here $P_n$ is the set of pairings of the $2n$ positions, i.e. of fixed-point-free involutions of
--   $\{0,\dots,2n-1\}$, and each pair $\{i, \sigma(i)\}$ contributes one factor.
--
--   This is the identity that assigns a value to a Feynman diagram of the free theory: each of the
--   $2n$ field insertions is a dangling half-line, a pairing joins the half-lines into $n$ lines, and
--   each line contributes its propagator, the two-point function of its endpoints. In the article's
--   field-mode notation the two-point function is $\delta(k_i - k_j)/k_i^2$; here it is the covariance
--   of the Gaussian vector, so the momentum-conserving delta function is carried by the covariance
--   matrix.
--
--   **Formalization Note.** Gaussianity is Mathlib's `IsGaussian`; centering is the explicit
--   hypothesis on coordinate means. Nothing is assumed about the covariance, so degenerate Gaussians
--   and repeated labels $k_i = k_j$ are included — the case the source treats separately under
--   "higher Gaussian moments". For $n = 0$ both sides equal $1$.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib
import Definitions.Def_FeynmanWickPairings
open MeasureTheory ProbabilityTheory

namespace FeynmanWick

theorem wick_theorem_gaussian {d n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian μ]
    (hcent : ∀ i : Fin d, ∫ x, x i ∂μ = 0) (k : Fin (2 * n) → Fin d) :
    ∫ x, ∏ j : Fin (2 * n), x (k j) ∂μ
      = wickSum (fun a b => ∫ x, x (k a) * x (k b) ∂μ) := by sorry

end FeynmanWick
