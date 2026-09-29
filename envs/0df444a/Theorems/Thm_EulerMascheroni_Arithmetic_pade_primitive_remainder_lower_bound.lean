-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_primitive_remainder_lower_bound
-- name    : EulerMascheroni.Arithmetic.pade_primitive_remainder_lower_bound
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T21:37:34.723371+00:00
-- url     : https://prove2.me/theorems/f3009478-0680-4068-9657-d32ba35b8893
-- title:
--   Explicit lower bound after exact Padé gcd cancellation
-- statement:
--   Write $R_N=Q_N\delta-P_N$ and $g_N=\gcd(P_N,Q_N)$ for the classical integer Padé sequences and the Euler–Gompertz constant. For every $n\ge0$ and integer $K>0$,
--   $$\frac{(n+1)!K^{n+1}}{(K+1)^{n+1}3^{K+1}(K+2)\gcd(Q_{n+1},(n!)^2)}\le\frac{R_{n+1}}{g_{n+1}}.$$
--   Thus the exact primitive integer linear form has an explicit rational lower bound, whose denominator depends only on $Q_{n+1}$ and a factorial. This combines the proved positive integral remainder estimate with the proved exact cancellation theorem. The latter uses adjacent denominator coprimality and the modular structure theorem.
--
--   The bound is unconditional. It supplies nonvanishing for the existing conditional Gompertz transcendence sketch, and can also certify that a proposed gcd-normalized approximation is too large at a specified index. It asserts neither convergence of these primitive forms to zero nor an asymptotic bound for their gcds.
-- source:
--   Explicit combination of the accepted Prove2Me exact Padé cancellation and positive remainder theorems. Classical approximation family: Hessami Pilehrood and Hessami Pilehrood, https://arxiv.org/abs/1010.1420, Euler–Gompertz continued fraction (34).

import Definitions.Def_eulerMascheroni_padeTransform
open EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.pade_primitive_remainder_lower_bound (n K : ℕ) (hK : 0 < K) :
    ((n+1).factorial:ℝ)*(K:ℝ)^(n+1) /
      (((K:ℝ)+1)^(n+1) * 3^(K+1) * ((K:ℝ)+2) *
        (Int.gcd (padeQ (n+1)) ((n.factorial:ℤ)^2):ℝ)) ≤
    ((padeQ (n+1):ℝ)*EulerMascheroni.gompertzConstant-(padeP (n+1):ℝ)) /
      (Int.gcd (padeP (n+1)) (padeQ (n+1)):ℝ) := by sorry
