-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_normalized_form_integral
-- name    : EulerMascheroni.Arithmetic.pade_normalized_form_integral
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:11:58.55596+00:00
-- url     : https://prove2.me/theorems/1d8ee7ba-5db5-4f5f-8fb0-853ce1809bff
-- title:
--   Common denominators give integral normalized Padé forms
-- statement:
--   If $d q_k(a)$ is an algebraic integer for all $k\le2n$, then
--
--   $$\frac{d(Q_na-P_n)}{(n!)^2}$$
--
--   is an algebraic integer. This is the exact arithmetic input needed for the norm obstruction.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11). The normalization and algebraic-norm argument are an elementary derivation for this decomposition; the arithmetic division conjecture is not assumed in the unconditional lemmas.

import Definitions.Def_eulerMascheroni_padeTransform
open Filter EulerMascheroni.Arithmetic
open scoped Topology

theorem EulerMascheroni.Arithmetic.pade_normalized_form_integral (a : ℝ) (n d : ℕ)
    (h : ∀ k : ℕ, k ≤ 2*n → IsIntegral ℤ ((d:ℝ)*quotientCoeff a k)) :
    IsIntegral ℤ ((d:ℝ)*((padeQ n:ℝ)*a-(padeP n:ℝ))/(n.factorial:ℝ)^2) := by sorry
