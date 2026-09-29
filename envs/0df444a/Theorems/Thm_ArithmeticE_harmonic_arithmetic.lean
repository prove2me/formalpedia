-- Prove2me | Theorems.Thm_ArithmeticE_harmonic_arithmetic
-- name    : ArithmeticE.harmonic_arithmetic
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:53:01.020261+00:00
-- url     : https://prove2.me/theorems/e6294ba0-0977-449b-83ab-2bf4f8404c88
-- title:
--   Exponential coefficient and common-denominator bounds for harmonic numbers
-- statement:
--   The rational sequence $H_n=\sum_{k=1}^n1/k$ has exponentially bounded absolute values and exponentially bounded positive common denominators. Explicit denominators are $D_n=\operatorname{lcm}(1,\ldots,n)$; Chebyshev's estimate bounds $D_n$ by $\exp((\log4+4)n)$. These are the arithmetic coefficient conditions for $e^z\operatorname{Ein}(z)$.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, pp. 1–6, especially Corollary 2.2 and Theorem 3.2. Explicit specialization and arithmetic verification for the Euler system.

import Definitions.Def_rationalEArithmetic

theorem ArithmeticE.harmonic_arithmetic : ArithmeticE.RationalArithmetic harmonic := by sorry
