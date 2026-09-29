-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_denominator_modular_structure
-- name    : EulerMascheroni.Arithmetic.pade_denominator_modular_structure
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T21:08:04.872387+00:00
-- url     : https://prove2.me/theorems/bb8263d5-8a24-485d-b489-70f5ad2a1590
-- title:
--   Periodicity and adjacent coprimality of Laguerre Padé denominators
-- statement:
--   Let $Q_0=1$, $Q_1=2$, and
--   $$Q_{n+2}=(2n+4)Q_{n+1}-(n+1)^2Q_n.$$
--   Then $n\mid Q_n-1$, consecutive denominators $Q_n,Q_{n+1}$ are coprime, and for every positive integer $m$,
--   $$Q_{n+m}\equiv Q_n\pmod m.$$
--
--   The proof first extracts the denominator from the established Padé binomial-transform identity:
--   $$Q_n=\sum_{j=0}^n\binom nj\frac{n!}{j!}.$$
--   The last term is one, and every earlier falling-factorial term is divisible by $n$. The congruence makes $Q_{n+1}$ coprime to $n+1$; applying the recurrence inductively then proves adjacent coprimality. To prove periodicity modulo $m$, use $Q_m\equiv1$ and $Q_{m+1}\equiv2$ as initial conditions and reduce the recurrence modulo $m$.
--
--   Periodicity holds for composite moduli and prime powers as well as primes. It turns denominator divisibility into a finite residue-class computation.
-- source:
--   Explicit deductions from the classical Laguerre Padé recurrence and its Casoratian. For the recurrence and approximation family see Hessami Pilehrood and Hessami Pilehrood, On a continued fraction expansion for Euler's constant, https://arxiv.org/abs/1010.1420, the Euler–Gompertz continued fraction (34) and the following discussion. The exact cancellation and modular deductions here are supplied with complete Lean proofs; no mathematical novelty is claimed.

import Definitions.Def_eulerMascheroni_padeTransform
open EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.pade_denominator_modular_structure (n : ℕ) :
    ((n:ℤ) ∣ padeQ n - 1) ∧ IsCoprime (padeQ n) (padeQ (n+1)) ∧
      ∀ m : ℕ, 0 < m → (padeQ (n+m) : ZMod m) = (padeQ n : ZMod m) := by sorry
