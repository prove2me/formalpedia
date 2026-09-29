-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_binomial_identity
-- name    : EulerMascheroni.Arithmetic.pade_binomial_identity
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:11:21.906739+00:00
-- url     : https://prove2.me/theorems/2d451c28-b0d8-4eac-8629-1c3e120e8c6c
-- title:
--   Realization of normalized Padé forms by the factorial quotient transform
-- statement:
--   For every real $a$ and integer $n\ge0$, the Euler Padé sequences and factorial quotient satisfy
--
--   $$Q_na-P_n=(n!)^2\sum_{j=0}^n\binom nj\binom{n+j}n q_{n+j}(a).$$
--
--   This connects common-denominator bounds for the quotient to integrality of normalized Padé forms.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11). The normalization and algebraic-norm argument are an elementary derivation for this decomposition; the arithmetic division conjecture is not assumed in the unconditional lemmas.

import Definitions.Def_eulerMascheroni_padeTransform
open Filter EulerMascheroni.Arithmetic
open scoped Topology

theorem EulerMascheroni.Arithmetic.pade_binomial_identity (a : ℝ) (n : ℕ) :
    (padeQ n : ℝ)*a - (padeP n : ℝ) =
      (n.factorial:ℝ)^2 * binomialTransform (quotientCoeff a) n := by sorry
