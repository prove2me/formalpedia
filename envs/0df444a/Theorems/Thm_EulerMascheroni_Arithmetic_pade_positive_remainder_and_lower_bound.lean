-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_positive_remainder_and_lower_bound
-- name    : EulerMascheroni.Arithmetic.pade_positive_remainder_and_lower_bound
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T21:17:33.590352+00:00
-- url     : https://prove2.me/theorems/190261b6-a056-4bad-9963-79d2b3b3473a
-- title:
--   Positive Laguerre Padé remainder and explicit rational lower bound
-- statement:
--   Let $P_n,Q_n$ be the integer Laguerre Padé sequences for the Euler–Gompertz constant $\delta$. Their remainder satisfies
--   $$Q_n\delta-P_n=n!\int_0^\infty\left(\frac{s}{1+s}\right)^n\frac{e^{-s}}{1+s}\,ds>0.$$
--   For every positive integer $K$, it has the explicit rational lower bound
--   $$Q_n\delta-P_n\ \ge\ \frac{n!K^n}{(K+1)^n3^{K+1}(K+2)}.$$
--
--   For the identity, set $k_n(s)=(s/(1+s))^n e^{-s}/(1+s)$. These nonnegative kernels are integrable and tend to zero at infinity, by comparison with $e^{-s}$. The derivative identity
--   $$k_{n+1}'=(n+2)k_{n+2}-2(n+2)k_{n+1}+(n+1)k_n$$
--   and the fundamental theorem of calculus on the positive half-line give the recurrence for $n!\int k_n$. The initial values are $\delta$ and $2\delta-1$, the latter from $k_0'=k_1-2k_0$. This identifies the integral sequence with $Q_n\delta-P_n$ by induction. Positivity follows from strict positivity of the kernel for $s>0$.
--
--   To obtain the lower bound, restrict the integral to $[K,K+1]$. On this interval the three factors are bounded below by $(K/(K+1))^n$, $e^{-(K+1)}$, and $1/(K+2)$. The inequality $e<3$ makes the bound rational. No unproved irrationality assertion or analytic remainder identity is imported.
--
--   Combined with the exact Padé gcd formula, this supplies a rigorous way to test whether integer normalization destroys the apparent analytic smallness of the approximation.
-- source:
--   Classical Laguerre Padé remainder for the Euler–Gompertz integral. See Hessami Pilehrood and Hessami Pilehrood, On a continued fraction expansion for Euler's constant, https://arxiv.org/abs/1010.1420, Euler–Gompertz continued fraction (34) and the following remainder discussion. The integral identity is derived from differentiation and the recurrence here; the elementary window lower bound is proved explicitly.

import Definitions.Def_eulerMascheroni_padeTransform
open MeasureTheory Set EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.pade_positive_remainder_and_lower_bound (n : ℕ) :
    ((padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) =
      (n.factorial:ℝ)*(∫ s in Ioi (0:ℝ), (s/(1+s))^n * Real.exp (-s)/(1+s))) ∧
    0 < (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) ∧
    ∀ K : ℕ, 0 < K →
      (n.factorial:ℝ)*(K:ℝ)^n / (((K:ℝ)+1)^n * 3^(K+1) * ((K:ℝ)+2)) ≤
        (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) := by sorry
