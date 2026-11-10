-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_f_infinity_series_bounds
-- name    : EntanglingOps.BinaryPhase.f_infinity_series_bounds
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-09T15:46:41.747747+00:00
-- url     : https://prove2.me/theorems/d14f292a-8530-4e70-90a8-00123297a1e4
-- title:
--   Convergence and value of $f_\infty=\frac1\pi\sum_k 2^k E(\psi_{\pi/2^k})\in(5.97931,5.97932)$
-- statement:
--   Let $\alpha_k=\pi/2^k$ and let $E(\psi_{\alpha})=-\cos^2\alpha\,\log_2\cos^2\alpha-\sin^2\alpha\,\log_2\sin^2\alpha$ be the entanglement (binary entropy of the Schmidt coefficients) of the resource state $|\psi_\alpha\rangle$ of Eq. (10). For $T(k)=2^k E(\psi_{\alpha_k})$, the series $\sum_{k\ge1}T(k)$ converges, every partial sum is strictly below the full sum, and
--
--   $$5.97931<f_\infty=\frac1\pi\sum_{k=1}^{\infty}2^k E(\psi_{\alpha_k})<5.97932 .$$
--
--   Role: the analytic and numerical part of Eq. (13) of the parent `binary_phase_protocol`: convergence of the series defining $f_\infty$, $f_N<f_\infty$, and the value $f_\infty\approx5.97932$; the parent supplies $E(\psi_\alpha)$ as the explicit binary entropy.
--
--   **Formalization Note**: $E(\psi_{\alpha_k})$ is written out as the binary entropy of $\cos^2\alpha_k$ (the reduced state of $|\psi_\alpha\rangle$ has eigenvalues $\cos^2\alpha,\sin^2\alpha$), passed through the hypothesis `hT`; the printed value $f_\infty=5.97932$ is stated as the two-sided bound, as in the parent.
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, https://arxiv.org/abs/quant-ph/0007057, p. 3, Eq. (13) and the value of f_infinity; Eq. (10) for the resource states

import Mathlib

namespace EntanglingOps.BinaryPhase

theorem f_infinity_series_bounds (T : ℕ → ℝ)
    (hT : ∀ k : ℕ, T k = (2 : ℝ) ^ k * -(Real.cos (Real.pi / 2 ^ k) ^ 2 *
        Real.logb 2 (Real.cos (Real.pi / 2 ^ k) ^ 2) +
      Real.sin (Real.pi / 2 ^ k) ^ 2 * Real.logb 2 (Real.sin (Real.pi / 2 ^ k) ^ 2))) :
    Summable (fun k : ℕ => T (k + 1)) ∧
    (∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, T k < ∑' k : ℕ, T (k + 1)) ∧
    (5.97931 : ℝ) < (1 / Real.pi) * ∑' k : ℕ, T (k + 1) ∧
    (1 / Real.pi) * ∑' k : ℕ, T (k + 1) < 5.97932 := by sorry

end EntanglingOps.BinaryPhase
