-- Prove2me | Theorems.Thm_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue
-- name    : Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/e47a6b33-14fd-5c4d-b007-821efe85b9bf
-- title:
--   Residue theorem for a radially parametrised star-shaped loop
-- statement:
--   Fix a centre $c \in \mathbb{C}$ and a radius function $r : \mathbb{R} \to \mathbb{R}$ that is continuous, periodic with period $2\pi$, and everywhere positive. Assume $r$ is piecewise twice continuously differentiable with respect to a finite subdivision: there are $N \in \mathbb{N}$ and $\varphi : \mathrm{Fin}(N+1) \to \mathbb{R}$ strictly increasing with $\varphi_0 = 0$ and $\varphi_N = 2\pi$, such that $r$ is $C^2$ on each closed interval $[\varphi_i, \varphi_{i+1}]$. Let $f : \mathbb{C} \to \mathbb{C}$, let $P \subset \mathbb{C}$ be a finite set, and let $\mathrm{res} : \mathbb{C} \to \mathbb{C}$ be any function. Assume: each $p \in P$ lies strictly inside the region, i.e. $\lVert p - c\rVert < r(\arg(p-c))$; $f$ is analytic at every $z$ with $\lVert z - c\rVert \le r(\arg(z-c))$ that is not in $P$; and at each $p \in P$ there is a function $g$ analytic at $p$ with $f(z) = \mathrm{res}(p)/(z-p) + g(z)$ for all $z$ near $p$ with $z \ne p$. The conclusion is the identity $$\int_0^{2\pi} f\bigl(c + r(\varphi)e^{i\varphi}\bigr)\,\bigl(r'(\varphi) + i\,r(\varphi)\bigr)e^{i\varphi}\,d\varphi = 2\pi i \sum_{p \in P} \mathrm{res}(p),$$ the contour integral being written out in the radial parametrisation.
--
--   This is the residue theorem for the closed piecewise-$C^2$ loop $\varphi \mapsto c + r(\varphi)e^{i\varphi}$ bounding the compact star-shaped region $\{z : \lVert z-c\rVert \le r(\arg(z-c))\}$, in the case of at most simple poles with prescribed residues. It is deduced from the Green-type formula [`Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral`](thm.html#Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral) for such loops, and is used in the cell-dissection construction of the reciprocity law, where sums of residues against primitives are compared with sums of jumps along edges.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex in

theorem Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (f : ℂ → ℂ) (P : Finset ℂ) (res : ℂ → ℂ)
    (hint : ∀ p ∈ P, ‖p - c‖ < r (arg (p - c)))
    (han : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∉ P → AnalyticAt ℂ f z)
    (hpole : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in nhdsWithin p {p}ᶜ, f z = res p / (z - p) + g z) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        f (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) =
      2 * Real.pi * I * ∑ p ∈ P, res p := by sorry
