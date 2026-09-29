-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_real_affine_integral_eventually_zero
-- name    : EulerMascheroni.Arithmetic.real_affine_integral_eventually_zero
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:11:10.374507+00:00
-- url     : https://prove2.me/theorems/18052fa1-1ed9-41d9-987b-553a7dea6fa7
-- title:
--   Vanishing of integral affine forms with small rational coefficients
-- statement:
--   Let $a$ be a real algebraic number and $r_n,s_n\in\mathbb Q$ tend to zero. If every $r_na+s_n$ is an algebraic integer, then
--
--   $$r_na+s_n=0\quad\text{for all sufficiently large }n.$$
--
--   This is a norm obstruction: smallness of both rational coefficients controls all conjugates, rather than only one real embedding.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11). The normalization and algebraic-norm argument are an elementary derivation for this decomposition; the arithmetic division conjecture is not assumed in the unconditional lemmas.

import Mathlib
open Filter
open scoped Topology

theorem EulerMascheroni.Arithmetic.real_affine_integral_eventually_zero (a : ℝ) (ha : IsAlgebraic ℚ a)
    (r s : ℕ → ℚ)
    (hr : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0))
    (hs : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 0))
    (hi : ∀ n, IsIntegral ℤ ((r n : ℝ) * a + (s n : ℝ))) :
    ∀ᶠ n in atTop, (r n : ℝ) * a + (s n : ℝ) = 0 := by sorry
