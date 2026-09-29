-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_no_small_integral_pade_forms
-- name    : EulerMascheroni.Arithmetic.no_small_integral_pade_forms
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:12:10.006908+00:00
-- url     : https://prove2.me/theorems/4ab5e9a4-9859-4704-8c0c-1e2b32d0ac0f
-- title:
--   Algebraic parameters cannot have exponentially scaled integral normalized Padé forms
-- statement:
--   Let $P_n,Q_n$ be the Euler Padé sequences, and let $a\in\mathbb R$ be algebraic. For any $C\ge1$ and positive integers $D_n\le C^{2n+1}$, it is impossible that
--
--   $$\frac{D_n(Q_na-P_n)}{(n!)^2}\quad\text{is an algebraic integer for every }n.$$
--
--   The assertion combines factorial growth bounds, algebraic norms, and adjacent nonvanishing of the Padé forms. It has no arithmetic division hypothesis.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11). The normalization and algebraic-norm argument are an elementary derivation for this decomposition; the arithmetic division conjecture is not assumed in the unconditional lemmas.

import Definitions.Def_eulerMascheroni_padeTransform
open Filter EulerMascheroni.Arithmetic
open scoped Topology

theorem EulerMascheroni.Arithmetic.no_small_integral_pade_forms (a : ℝ) (ha : IsAlgebraic ℚ a)
    (C : ℝ) (hC : 1 ≤ C) (D : ℕ → ℕ)
    (hDpos : ∀ n, 0 < D n) (hD : ∀ n, (D n : ℝ) ≤ C^(2*n+1))
    (hi : ∀ n, IsIntegral ℤ
      ((D n:ℝ)*((padeQ n:ℝ)*a-(padeP n:ℝ))/(n.factorial:ℝ)^2)) : False := by sorry
