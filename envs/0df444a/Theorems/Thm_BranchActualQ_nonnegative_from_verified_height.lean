-- Prove2me | Theorems.Thm_BranchActualQ_nonnegative_from_verified_height
-- name    : BranchActualQ.nonnegative_from_verified_height
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-18T09:44:24.458302+00:00
-- url     : https://prove2.me/theorems/761ca727-9e45-4612-8647-effd19439d32
-- title:
--   Original xi-derived Q hierarchy: nonnegativity from the verified zero range up to height 1000
-- statement:
--   Assume that every zero $s$ of the Riemann zeta function with $0<\Re s<1$ and $|\Im s|\le1000$ has real part $1/2$. Define
--   $$\xi(s)=\frac{1+s(s-1)\,\mathrm{completedRiemannZeta}_0(s)}2,\qquad G(x)=\Re\xi(1/2+\sqrt{x}),$$
--   $$Q_n(u)=2^n u^{2n-1}(-1)^{n-1}\left.\frac{d^n}{dx^n}\bigl(\log G(x)-\log G(0)\bigr)\right|_{x=u^2}.$$
--   Then $Q_n(u)\ge0$ for every integer $n\ge1$ and every real $u>0$. The low-height verification is the only hypothesis: zero geometry, multiplicity counting, the low positive anchor, the canonical product, and all scale estimates are supplied by concrete proofs.
-- source:
--   Desenvolvimento RH, repaired common argument for the finite and infinite off-critical branches, 2026-11-18. Original-Q cascade, three-scale exhaustion, and the compact-scale positivity proof; concrete analytic inputs from accepted project theorems.

import Mathlib

theorem BranchActualQ.nonnegative_from_verified_height (height : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 1000 → s.re = 1/2) :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n : ℕ), 1 ≤ n → ∀ u > 0, 0 ≤ Q n u := by sorry
