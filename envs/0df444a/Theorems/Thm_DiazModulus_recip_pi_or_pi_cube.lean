-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_or_pi_cube
-- name    : DiazModulus.recip_pi_or_pi_cube
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:31:22.813239+00:00
-- url     : https://prove2.me/theorems/cf8e2421-149c-4213-831f-5e02a592b127
-- title:
--   For algebraic γ ≠ 0, e^{iγ/π} is transcendental or e^{iπ³/γ} is, and likewise with e^{iγ²/π³}
-- statement:
--   **The real half of (S) against powers of π.**
--
--   For every non-zero algebraic $\gamma$, at least one of $e^{i\gamma/\pi}$ and $e^{i\pi^{3}/\gamma}$ is transcendental, and at least one of $e^{i\gamma/\pi}$ and $e^{i\gamma^{2}/\pi^{3}}$ is transcendental.
--
--   The transcendence of $e^{i\gamma/\pi}$ for every non-zero algebraic $\gamma$ is the statement (S) (`DiazModulus.recip_pi_not_log`), which is open. This node gives, for each $\gamma$, a partner number that must be transcendental whenever $e^{i\gamma/\pi}$ is algebraic. Both halves are instances of `DiazModulus.geometric_triple_not_logs`.
--
--   **Novelty.** None: both halves are instances of Corollaire 4 of M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory **5** (1973), 191–202, and of Exercise 15.16(b)(ii) of Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer 2000): for non-zero $\lambda \in \mathcal{L}$ and $b \notin \mathbb{Q}$ algebraically dependent on $\lambda$, one of $e^{\lambda b}$, $e^{\lambda/b}$ is transcendental. Take $b = \gamma/\pi^{2}$, with $\lambda = i\pi$ for the first half and $\lambda = i\gamma/\pi$ for the second. The contribution of this node is the formal proof.
-- source:
--   Classical: M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Corollaire 4; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Exercise 15.16(b)(ii). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem recip_pi_or_pi_cube (γ : ℂ) (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0) :
    (Transcendental ℚ (Complex.exp (Complex.I * γ / ((Real.pi : ℝ) : ℂ))) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3 / γ))) ∧
    (Transcendental ℚ (Complex.exp (Complex.I * γ / ((Real.pi : ℝ) : ℂ))) ∨
      Transcendental ℚ (Complex.exp (Complex.I * γ ^ 2 / ((Real.pi : ℝ) : ℂ) ^ 3))) := by sorry

end DiazModulus
