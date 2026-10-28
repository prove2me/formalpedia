-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_theorem_1
-- name    : ClassicalShadow.Linear.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:57.635975+00:00
-- url     : https://prove2.me/theorems/3dfefafd-a710-4e45-8f88-3b5784196caf
-- title:
--   Theorem 1, p. 13 — median of means over 2log(2M/δ) batches of (34/ε²)max‖O_i,0‖²_shadow shadows predicts all tr(O_iρ) to ±ε w.p. ≥ 1−δ
-- statement:
--   Fix a finite, tomographically complete measurement primitive $\mathcal U$ on $n$ qubits, an unknown state (density operator) $\rho$, a collection $O_1,\dots,O_M$ of $2^n\times 2^n$ Hermitian matrices ($M \ge 1$), and accuracy parameters $\epsilon, \delta \in (0,1]$. Let $K$ and $N \ge 1$ be integers with
--   $$K \ge 2\log\frac{2M}{\delta} \qquad\text{and}\qquad N \ge \frac{34}{\epsilon^2}\max_{1\le i\le M}\Big\|O_i - \frac{\operatorname{tr}(O_i)}{2^n}\mathbb I\Big\|_{\mathrm{shadow}}^2 ,$$
--   where $\|\cdot\|_{\mathrm{shadow}}$ is the shadow norm (S7). Take $NK$ independent classical shadows of $\rho$, split into $K$ batches of $N$, and let $\hat o_i(N,K)$ be the median of the $K$ batch means of $\operatorname{tr}(O_i\hat\rho_j)$ (S12). Then, with probability at least $1-\delta$,
--   $$|\hat o_i(N,K) - \operatorname{tr}(O_i\rho)| \le \epsilon \qquad\text{for all } 1 \le i \le M .$$
--
--   The total number of measurements, $NK = O\big(\log(M)\max_i \|O_{i,0}\|_{\mathrm{shadow}}^2/\epsilon^2\big)$, grows only logarithmically in the number of properties $M$ and does not depend on the dimension $2^n$ explicitly.
--
--   **Formalization Note.** $\log$ is the natural logarithm. The paper sets $K$ and $N$ equal to the displayed reals; here they are natural numbers at least those values, which includes the rounding up that a count of snapshots needs. $N \ge 1$ is added (if every $O_i$ is a multiple of $\mathbb I$ the formula gives $N = 0$), and $\epsilon > 0$, $\delta > 0$, $M \ge 1$ are added because at $\epsilon = 0$ or $\delta = 0$ the printed $N, K$ are undefined. The ensemble is finite with positive-weight completeness, and the median is the lower median; see the Setting file. Probabilities are finite sums over all $K\times N$ outcome arrays under the product of the single-snapshot law $w_i\langle b|U_i\rho U_i^\dagger|b\rangle$. The predictions and $\operatorname{tr}(O_i\rho)$ are real parts, which for Hermitian $O_i$ are the traces themselves.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 13, Theorem 1, (S13)–(S14)

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem theorem_1 {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hE : TomographicallyComplete E) (ρ : Op n) (hρ : WildeQIT.IsDensityOperator ρ)
    {M : ℕ} (hM : 1 ≤ M) (O : Fin M → Op n) (hO : ∀ i, (O i).IsHermitian)
    (ε δ : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1)
    (K N : ℕ) (hK : 2 * Real.log (2 * M / δ) ≤ K) (hN1 : 1 ≤ N)
    (hN : ∀ i, 34 / ε ^ 2 * shadowNorm E (traceless (O i)) ^ 2 ≤ N) :
    1 - δ ≤ sampleProb (K := K) (N := N) E ρ
      (fun ω => ∀ i, |momEstimate E (O i) ω - ((O i) * ρ).trace.re| ≤ ε) := by sorry
end ClassicalShadow.Linear
