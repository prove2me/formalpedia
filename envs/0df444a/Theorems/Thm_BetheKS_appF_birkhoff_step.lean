-- Prove2me | Theorems.Thm_BetheKS_appF_birkhoff_step
-- name    : BetheKS.appF_birkhoff_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:13.929907+00:00
-- url     : https://prove2.me/theorems/8ede71b7-5130-4add-8ffc-79a9476c291d
-- title:
--   App. F, p.27 — $\max_{\tau\in S_r}\sum_bD_{\tau(b),b}\ge\|D\|_F/r$ for zero-sum $D\ne0$
-- statement:
--   Let $D$ be a nonzero real $r\times r$ matrix with zero row sums and zero column sums. Then
--   $$
--   \max_{\tau\in S_r}\sum_bD_{\tau(b),b}\ \ge\ \frac{\|D\|_F}{r},
--   $$
--   where $\|D\|_F=(\sum_{a,b}D_{ab}^2)^{1/2}$. The paper derives it from Birkhoff's theorem, $\mathbf 1\mathbf 1^{\mathsf T}/r+D/(r\|D\|_F)$ being doubly stochastic. In App. F it is applied to the expected centered confusion matrix of the rounding.
--
--   Differences from the source:
--
--   - generalization: r ≥ 2 the number of communities → every r; reason: the statement is about r × r matrices; r ≥ 2 is a special case
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), App. F, proof of Theorem 2.3, p.27 (PDF p.28), display "For any such nonzero matrix D"

import Mathlib

set_option autoImplicit false

namespace BetheKS

/-- **App. F, proof of Theorem 2.3 (Birkhoff step)** — Dong, McKenzie, arXiv:2610.41802 (held version,
sha256 4da41e16…), p.27 (PDF p.28): for any nonzero real `r × r` matrix `D` with zero row and column
sums, `max_{τ ∈ S_r} ∑_b D_{τ(b), b} ≥ ‖D‖_F / r`.

**Formalization Note.** `‖D‖_F = (∑_{a,b} D_{ab}²)^{1/2}`; the maximum is a finite `sup'` over
`Equiv.Perm (Fin r)`. The statement is for every `r`. -/
theorem appF_birkhoff_step {r : ℕ} (D : Matrix (Fin r) (Fin r) ℝ) (hD : D ≠ 0)
    (hrow : ∀ a, ∑ b, D a b = 0) (hcol : ∀ b, ∑ a, D a b = 0) :
    Real.sqrt (∑ a, ∑ b, D a b ^ 2) / r ≤
      Finset.univ.sup' Finset.univ_nonempty (fun τ : Equiv.Perm (Fin r) => ∑ b, D (τ b) b) := by sorry

end BetheKS
