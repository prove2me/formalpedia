-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_per_feature_bound
-- name    : ClassicalShadow.Linear.per_feature_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:44.639899+00:00
-- url     : https://prove2.me/theorems/f69184ee-4d27-4903-92bf-b93b3d3357f0
-- title:
--   p. 13, proof of Theorem 1 — with N, K as in (S13), each Pr[|ô_i(N,K) − tr(O_iρ)| ≥ ε] ≤ δ/M
-- statement:
--   Let $\mathcal U$ be a finite, tomographically complete measurement primitive on $n$ qubits, $\rho$ a density operator, $O_1,\dots,O_M$ Hermitian $2^n \times 2^n$ matrices ($M \ge 1$), and $\epsilon, \delta \in (0,1]$. Let $K$ and $N \ge 1$ be integers with
--   $$K \ge 2\log\frac{2M}{\delta}, \qquad N \ge \frac{34}{\epsilon^2}\,\Big\|O_i - \frac{\operatorname{tr}(O_i)}{2^n}\mathbb I\Big\|_{\mathrm{shadow}}^2 \quad (1 \le i \le M).$$
--   From $NK$ independent classical shadows of $\rho$, let $\hat o_i(N,K)$ be the median-of-means prediction (S12) of $\operatorname{tr}(O_i\rho)$. Then for every $1 \le i \le M$,
--   $$\Pr\big[\,|\hat o_i(N,K) - \operatorname{tr}(O_i\rho)| \ge \epsilon\,\big] \le \frac{\delta}{M}.$$
--
--   A union bound over the $M$ observables then gives Theorem 1.
--
--   **Formalization Note.** $\log$ is the natural logarithm. $N$ and $K$ are natural numbers at least the printed real values of (S13); $N \ge 1$, $\epsilon > 0$, $\delta > 0$ and $M \ge 1$ are added because at $\epsilon = 0$ or $\delta = 0$ the printed values are undefined. Probabilities are finite sums over all outcome arrays under the product of the single-snapshot law.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 13, proof of Theorem 1

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem per_feature_bound {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hE : TomographicallyComplete E) (ρ : Op n) (hρ : WildeQIT.IsDensityOperator ρ)
    {M : ℕ} (hM : 1 ≤ M) (O : Fin M → Op n) (hO : ∀ i, (O i).IsHermitian)
    (ε δ : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1)
    (K N : ℕ) (hK : 2 * Real.log (2 * M / δ) ≤ K) (hN1 : 1 ≤ N)
    (hN : ∀ i, 34 / ε ^ 2 * shadowNorm E (traceless (O i)) ^ 2 ≤ N) :
    ∀ i, sampleProb (K := K) (N := N) E ρ
      (fun ω => ε ≤ |momEstimate E (O i) ω - ((O i) * ρ).trace.re|) ≤ δ / M := by sorry
end ClassicalShadow.Linear
