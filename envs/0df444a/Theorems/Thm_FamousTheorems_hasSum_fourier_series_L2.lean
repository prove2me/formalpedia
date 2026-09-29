-- Prove2me | Theorems.Thm_FamousTheorems_hasSum_fourier_series_L2
-- name    : FamousTheorems.hasSum_fourier_series_L2
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:45:31.731045+00:00
-- url     : https://prove2.me/theorems/dd2ea37c-aec6-4cbd-a291-ef338ab83e73
-- title:
--   Fourier series converge in the mean square
-- statement:
--   **Convergence of Fourier series in $L^2$** (the Riesz–Fischer theorem).
--
--   For every square-integrable function $f$ on the circle $\mathbb{R}/T\mathbb{Z}$, the Fourier series
--   $$\sum_{n \in \mathbb{Z}} \hat{f}(n)\, e_n, \qquad \hat{f}(n) = \frac{1}{T}\int_0^T f(x)e^{-2\pi i nx/T}\,dx,$$
--   converges to $f$ in the $L^2$ norm.
--
--   The exponentials $\{e_n\}_{n \in \mathbb{Z}}$ form a complete orthonormal basis of $L^2$ of the
--   circle, so this is the statement that the Fourier expansion loses nothing. Convergence is
--   unconditional — `HasSum` quantifies over finite partial sums with no ordering — which is what makes
--   $L^2$ the natural home for Fourier analysis: pointwise convergence is delicate (du Bois-Reymond
--   constructed a continuous function whose Fourier series diverges at a point, and Carleson's theorem
--   that it converges almost everywhere took until 1966), while mean-square convergence is clean and
--   holds for every $f$.
--
--   Fourier asserted in 1807 that every function admits such an expansion, which was not believed;
--   Dirichlet gave the first convergence proof under restrictive hypotheses in 1829. The definitive $L^2$
--   statement is the Riesz–Fischer theorem of 1907, and with it Parseval's identity
--   $\lVert f\rVert_2^2 = \sum_n |\hat{f}(n)|^2$.
--
--   **Formalization note.** `haarAddCircle` is the normalized Haar probability measure on the circle, and
--   `fourierLp 2 i` is the $i$-th exponential viewed as an element of $L^2$. The result is Mathlib's
--   `MeasureTheory.hasSum_fourier_series_L2`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Real Topology ENNReal

theorem hasSum_fourier_series_L2 {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    HasSum (fun i => fourierCoeff (f : AddCircle T → ℂ) i • fourierLp 2 i) f := by sorry

end FamousTheorems
