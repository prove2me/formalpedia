-- Prove2me | Theorems.Thm_ArithmeticE_series_summable
-- name    : ArithmeticE.series_summable
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:53:01.003421+00:00
-- url     : https://prove2.me/theorems/91eaa6a3-f258-420b-8f3a-0fc8561aa994
-- title:
--   Arithmetic E-series coefficients give absolute convergence at every complex point
-- statement:
--   If a formal series has rational factorial-normalized coefficients satisfying the E-function arithmetic bounds, then its series converges absolutely at every complex point. The estimate follows by comparison with a constant multiple of the exponential series at $C|z|$. Thus canonical series evaluation is justified without a separate convergence assumption.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, pp. 1–6, especially Corollary 2.2 and Theorem 3.2. Explicit specialization and arithmetic verification for the Euler system.

import Definitions.Def_rationalEArithmetic
open ArithmeticE

theorem ArithmeticE.series_summable (f : PowerSeries ℂ) (hf : RationalSeriesArithmetic f) (z : ℂ) :
    Summable (fun n : ℕ => PowerSeries.coeff n f * z^n) := by sorry
