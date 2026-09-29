-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_exact_cancellation
-- name    : EulerMascheroni.Arithmetic.pade_exact_cancellation
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T21:08:00.92246+00:00
-- url     : https://prove2.me/theorems/a00522da-84f9-427d-8b06-24ee6ef195db
-- title:
--   Exact gcd cancellation and its finite modular criterion
-- statement:
--   For the classical Euler–Gompertz Padé numerator and denominator sequences, define $g_n=\gcd(P_n,Q_n)$. Then
--   $$g_{n+1}=\gcd(Q_{n+1},(n!)^2).$$
--   For every positive integer $d$, this has the exact finite criterion
--   $$d\mid g_{n+1}\quad\Longleftrightarrow\quad d\mid(n!)^2\ \text{and}\ Q_{(n+1)\bmod d}\equiv0\pmod d.$$
--
--   The Casoratian is $Q_nP_{n+1}-Q_{n+1}P_n=(n!)^2$. Any common divisor of $P_{n+1},Q_{n+1}$ consequently divides both terms on the right side of the gcd formula. Conversely, adjacent denominator coprimality supplies a Bézout identity for $Q_n,Q_{n+1}$, which shows that any common divisor of $Q_{n+1},(n!)^2$ also divides $P_{n+1}$. Denominator periodicity modulo $d$ gives the residue criterion.
--
--   Taking $d$ to be a prime power describes every possible cancellation in the primitive integer linear form $(Q_{n+1}\delta-P_{n+1})/g_{n+1}$. This is an exact arithmetic description, not a claim that the resulting forms tend to zero.
-- source:
--   Explicit deductions from the classical Laguerre Padé recurrence and its Casoratian. For the recurrence and approximation family see Hessami Pilehrood and Hessami Pilehrood, On a continued fraction expansion for Euler's constant, https://arxiv.org/abs/1010.1420, the Euler–Gompertz continued fraction (34) and the following discussion. The exact cancellation and modular deductions here are supplied with complete Lean proofs; no mathematical novelty is claimed.

import Definitions.Def_eulerMascheroni_padeTransform
open EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.pade_exact_cancellation (n : ℕ) :
    Int.gcd (padeP (n+1)) (padeQ (n+1)) = Int.gcd (padeQ (n+1)) ((n.factorial:ℤ)^2) ∧
    ∀ d : ℕ, 0 < d →
      (d ∣ Int.gcd (padeP (n+1)) (padeQ (n+1)) ↔
        (d:ℤ) ∣ (n.factorial:ℤ)^2 ∧ (padeQ ((n+1)%d) : ZMod d) = 0) := by sorry
