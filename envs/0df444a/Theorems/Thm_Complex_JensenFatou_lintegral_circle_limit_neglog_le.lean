-- Prove2me | Theorems.Thm_Complex_JensenFatou_lintegral_circle_limit_neglog_le
-- name    : Complex.JensenFatou.lintegral_circle_limit_neglog_le
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-16T00:27:11.313625+00:00
-- url     : https://prove2.me/theorems/0d4f2558-9e74-49e8-b81f-d129f8a9e319
-- title:
--   Jensen–Fatou bound for logarithms of limits along concentric circles
-- statement:
--   Let $f$ be holomorphic on the complex open unit disk, with $|f(z)|\le1$ there and $f(0)\ne0$. Let $r_n\in(0,1)$ be any sequence of radii and suppose that
--
--   $$f(r_ne^{it})\longrightarrow g(t)$$
--
--   for Lebesgue almost every $t\in(0,2\pi]$. Then the nonnegative extended negative logarithm of the limit obeys
--
--   $$\int_0^{2\pi}\max\{0,-\log|g(t)|\}\,dt\le-2\pi\log|f(0)|.$$
--
--   At $g(t)=0$, the integrand is $+\infty$. In particular its integral is finite, and $g$ is nonzero almost everywhere. The theorem requires convergence of the displayed function values; it does not require convergence of the radii themselves. Taking radii tending to one gives the usual boundary version.
--
--   This is a Jensen–Fatou estimate used to transfer the disk logarithmic submean inequality to the boundary in the conformal proof of scalar Hirschman interpolation. The statement assumes the almost everywhere limit, and does not assert the separate Fatou theorem giving existence of radial limits.
-- source:
--   Supporting analytic lemma for the conformal proof of Hirschman interpolation: Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 12.2.2, pp.369–370. Derived from Jensen’s formula and Fatou’s lemma; Jensen implementation: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/JensenFormula.lean (AnalyticOnNhd.circleAverage_log_norm). This circle-limit supporting formulation is not quoted as a numbered theorem of Wilde.

import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
open Filter MeasureTheory
open scoped Topology ENNReal

namespace Complex.JensenFatou
theorem lintegral_circle_limit_neglog_le {f : ℂ → ℂ} {g : ℝ → ℂ} {r : ℕ → ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (hc : f 0 ≠ 0)
    (hr : ∀ n, 0 < r n ∧ r n < 1)
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hlim : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 (2*Real.pi)),
      Tendsto (fun n => f (circleMap 0 (r n) t)) atTop (𝓝 (g t))) :
    (∫⁻ t in Set.Ioc 0 (2*Real.pi), (-ENNReal.log (ENNReal.ofReal ‖g t‖)).toENNReal) ≤
      ENNReal.ofReal ((2*Real.pi)*(-Real.log ‖f 0‖)) := by sorry
end Complex.JensenFatou
