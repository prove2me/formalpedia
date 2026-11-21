-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_pow_bound_iteratedFDeriv
-- name    : FiniteEnergyPlane.exists_pow_bound_iteratedFDeriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T19:14:22.142498+00:00
-- url     : https://prove2.me/theorems/6313a31e-499e-408a-b68e-cc04a59518e1
-- title:
--   Uniform power-form bounds for finitely many derivatives on an end
-- statement:
--   Let $F$ be a real normed space and $X:\mathbb{R}\times\mathbb{R}\to F$. Suppose that for every $m\ge 1$ there are $C_m$ and $s_m$ with $\|D^mX(s,t)\|\le C_m$ for all $s\ge s_m$ and all $t$. Then for every $n$ there are $D\ge 1$ and $s_1$ such that
--   $$\|D^iX(s,t)\|\le D^{\,i}\qquad\text{for all } 1\le i\le n,\ s\ge s_1,\ t\in\mathbb{R}.$$
--
--   This puts derivative bounds on a cylindrical end into the form $\|D^iX\|\le D^i$ that Faà di Bruno type estimates for compositions require.
--
--   **Formalization Note** Derivatives are `iteratedFDeriv ℝ`; "for large $s$" means `∀ s ≥ s₁`, uniformly in `t : ℝ`. The hypothesis covers orders `m ≥ 1` only.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379; setting of C. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012)

import Mathlib

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Power-form derivative bounds on an end. If every derivative of order `m ≥ 1` of
`X : ℝ × ℝ → F` is bounded for large `s`, uniformly in `t`, then for each `n` there are `D ≥ 1`
and `s₁` with `‖D^i X (s, t)‖ ≤ D ^ i` for all `1 ≤ i ≤ n`, `s ≥ s₁` and `t`. -/
theorem exists_pow_bound_iteratedFDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : ℝ × ℝ → F}
    (h : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m X (s, t)‖ ≤ C)
    (n : ℕ) : ∃ D s₁ : ℝ, 1 ≤ D ∧ ∀ i, 1 ≤ i → i ≤ n → ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i X (s, t)‖ ≤ D ^ i := by
  sorry

end FiniteEnergyPlane
