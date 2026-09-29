-- Prove2me | Theorems.Thm_Complex_exists_lipschitzWith_divided_minor
-- name    : Complex.exists_lipschitzWith_divided_minor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/36f0ba2c-2552-579b-b7a3-5c0be8617a88
-- title:
--   Lipschitz divided minors of a holomorphic map
-- statement:
--   Let $r$ be a natural number, $\varphi:\mathbb{C}\to(\mathrm{Fin}\,r\to\mathbb{C})$ a map, $c\in\mathbb{C}$ and $R$ a real number with $0<R$, and assume that for each index $i$ the coordinate function $z\mapsto\varphi(z)_i$ is complex differentiable on the open ball $B(c,R)$. Then there exist a radius $\rho>0$, a constant $L\ge 0$ and a function $\Psi:\mathbb{C}\to\mathbb{C}\to(\mathrm{Fin}\,r\times\mathrm{Fin}\,r\to\mathbb{C})$ such that three things hold. First, for all $w,z\in B(c,\rho)$ and every pair $p=(i,j)$ of indices, $\varphi(w)_i\varphi(z)_j-\varphi(w)_j\varphi(z)_i=(z-w)\,\Psi(w)(z)(p)$, so $\Psi$ is a factorisation of the $2\times 2$ minors by their vanishing on the diagonal. Secondly, for all $w\in B(c,\rho)$ and every pair $p=(i,j)$, the diagonal value is the Wronskian-type minor $\Psi(w)(w)(p)=\varphi(w)_i\,(\mathrm{d}/\mathrm{d}z)\varphi(z)_j|_{z=w}-\varphi(w)_j\,(\mathrm{d}/\mathrm{d}z)\varphi(z)_i|_{z=w}$, the derivatives being Mathlib's `deriv`. Thirdly, for all $w,z,z'\in B(c,\rho)$ one has $\|\Psi(w)(z)-\Psi(w)(z')\|\le L\|z-z'\|$, the norm being the supremum over the pairs $p$; thus $\Psi$ is Lipschitz in its second variable with a constant uniform in the base point $w$. For $r=0$ all three clauses are vacuous.
--
--   This is the elementary complex-analytic input recording that the $2\times 2$ minors $\varphi_i(w)\varphi_j(z)-\varphi_j(w)\varphi_i(z)$ of a holomorphic map into $\mathbb{C}^r$, which vanish on the diagonal, admit a divided form that is Lipschitz in $z$ uniformly in $w$ and restricts on the diagonal to the Wronskian minors of $(\varphi,\varphi')$. It is used in the construction of a hyperplane section with a lower bound on a sum of logarithms of secant values, in [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_lipschitzWith_divided_minor.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Metric

theorem Complex.exists_lipschitzWith_divided_minor {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R)) :
    ∃ ρ > 0, ∃ L ≥ 0, ∃ Ψ : ℂ → ℂ → (Fin r × Fin r → ℂ),
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          φ w p.1 * φ z p.2 - φ w p.2 * φ z p.1 = (z - w) * Ψ w z p) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ p : Fin r × Fin r,
          Ψ w w p = φ w p.1 * deriv (fun z ↦ φ z p.2) w - φ w p.2 * deriv (fun z ↦ φ z p.1) w) ∧
      (∀ w ∈ Metric.ball c ρ, ∀ z ∈ Metric.ball c ρ, ∀ z' ∈ Metric.ball c ρ,
          ‖Ψ w z - Ψ w z'‖ ≤ L * ‖z - z'‖) := by sorry
