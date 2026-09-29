-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_e_system_arithmetic
-- name    : EulerMascheroni.Mixed.e_system_arithmetic
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:53:21.004519+00:00
-- url     : https://prove2.me/theorems/a252dbde-47ab-4412-aa96-d6f4c02dfeee
-- title:
--   Arithmetic E-function coefficient conditions for the Euler system
-- statement:
--   Every component of the formal vector $(1,e^X,e^X\operatorname{Ein}(X))$ has rational factorial-normalized coefficients, exponentially bounded in absolute value, with exponentially bounded common denominators. The three normalized coefficient sequences are respectively the Kronecker delta at zero, the constant sequence one, and the harmonic numbers.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, pp. 1–6, especially Corollary 2.2 and Theorem 3.2. Explicit specialization and arithmetic verification for the Euler system.

import Definitions.Def_rationalEArithmetic
import Definitions.Def_eulerMascheroni_formalESystem
open ArithmeticE PowerSeries EulerMascheroni.Mixed

theorem EulerMascheroni.Mixed.e_system_arithmetic : ∀ i : Fin 3,
    RationalSeriesArithmetic (![1, PowerSeries.exp ℂ, formalExpEin] i) := by sorry
