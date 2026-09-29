-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_normalized_pade_tendsto_zero
-- name    : EulerMascheroni.Arithmetic.normalized_pade_tendsto_zero
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:11:09.462566+00:00
-- url     : https://prove2.me/theorems/2bb261cf-6fb1-4b91-ab82-7e6a342df853
-- title:
--   Exponential denominator factors are dominated by factorial normalization
-- statement:
--   Suppose $C\ge1$, $D_n\in\mathbb N$ satisfies $D_n\le C^{2n+1}$, and $U_n\in\mathbb Z$ satisfies $|U_n|\le4^n n!$. Then
--
--   $$\frac{D_nU_n}{(n!)^2}\longrightarrow0.$$
--
--   This gives simultaneous smallness of the two rational coefficients of a normalized Padé form.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11). The normalization and algebraic-norm argument are an elementary derivation for this decomposition; the arithmetic division conjecture is not assumed in the unconditional lemmas.

import Mathlib
open Filter
open scoped Topology

theorem EulerMascheroni.Arithmetic.normalized_pade_tendsto_zero (U : ℕ → ℤ) (C : ℝ) (hC : 1 ≤ C)
    (D : ℕ → ℕ) (hD : ∀ n, (D n : ℝ) ≤ C^(2*n+1))
    (hU : ∀ n, |U n| ≤ (4 : ℤ)^n*(n.factorial:ℤ)) :
    Tendsto (fun n => (D n : ℝ)*(U n : ℝ)/(n.factorial:ℝ)^2) atTop (𝓝 0) := by sorry
