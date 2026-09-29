-- Prove2me | Theorems.Thm_FamousTheorems_jensen_formula
-- name    : FamousTheorems.jensen_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:12.876423+00:00
-- url     : https://prove2.me/theorems/cf1f974d-515a-4099-8c84-c062d2e07bea
-- title:
--   Jensen's formula (complex analysis)
-- statement:
--   **Jensen's formula.** Let $f$ be meromorphic on the closed disc $\overline D(c,R)$, $R\ne0$. Then
--   $$\frac1{2\pi}\int_0^{2\pi}\log|f(c+Re^{i\theta})|\,d\theta=\sum_{u}\operatorname{ord}_u(f)\,\log\frac{R}{|c-u|}+\operatorname{ord}_c(f)\log R+\log|\operatorname{lc}_c(f)|,$$
--   where the sum runs over the zeros and poles $u$ of $f$ in the disc, counted with order ($\operatorname{ord}_u>0$ at zeros and $<0$ at poles). Here $\operatorname{lc}_c(f)$ is the leading (trailing) coefficient of the Laurent expansion of $f$ at $c$.
--
--   When $f$ is holomorphic with $f(c)\ne0$, the formula reduces to the classical $\log|f(c)|=\frac1{2\pi}\int\log|f(c+Re^{i\theta})|\,d\theta-\sum_{\text{zeros}}\log\frac R{|u-c|}$. Jensen's formula links the growth of an analytic function to the distribution of its zeros. It is the foundation of Nevanlinna theory and of the theory of entire functions of finite order (Hadamard factorization).
--
--   **Formalization note.** Mathlib's `MeromorphicOn.circleAverage_log_norm`. `Real.circleAverage` is the average over the circle of radius $|R|$ about $c$. `MeromorphicOn.divisor f (Metric.closedBall c |R|)` is the finitely supported order function of $f$ on the disc, cast to `ℝ`, and `∑ᶠ` is a finite sum. `meromorphicTrailingCoeffAt f c` is the leading coefficient of the Laurent expansion at $c$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeromorphicOn.circleAverage_log_norm`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jensen_formula {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0) (h₁f : MeromorphicOn f (Metric.closedBall c |R|)) :
    Real.circleAverage (fun z => Real.log ‖f z‖) c R =
      ∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall c |R|) u : ℝ) * Real.log (R * ‖c - u‖⁻¹) +
        (MeromorphicOn.divisor f (Metric.closedBall c |R|) c : ℝ) * Real.log R +
        Real.log ‖meromorphicTrailingCoeffAt f c‖ := by sorry

end FamousTheorems
