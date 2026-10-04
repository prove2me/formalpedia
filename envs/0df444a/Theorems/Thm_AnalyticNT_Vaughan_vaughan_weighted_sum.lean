-- Prove2me | Theorems.Thm_AnalyticNT_Vaughan_vaughan_weighted_sum
-- name    : AnalyticNT.Vaughan.vaughan_weighted_sum
-- status  : Proved
-- author  : @Patrick
-- created : 2026-09-07T03:57:41.585639+00:00
-- url     : https://prove2.me/theorems/81b6f270-6299-4aa5-abad-61f9f508a218
-- title:
--   Vaughan decomposition with arbitrary finite complex weights
-- statement:
--   Vaughan’s identity decomposes the von Mangoldt function into a small direct term, two Type-I terms, and a Type-II term. This theorem multiplies the identity by an arbitrary complex weight and sums over any finite set. It therefore accommodates smooth cutoffs, coprimality restrictions, and Fourier characters together. The Type-II term retains the complete Möbius divisor coefficient. No bound on the size of these terms is asserted.
-- source:
--   Vaughan, An elementary method in prime number theory (1980); adapted from Gershon Bialer, https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/ext/analytic_nt/AnalyticNT/Vaughan/Identity.lean, with arbitrary-weight extension.

import Definitions.Def_AnalyticNT_Vaughan
open AnalyticNT.Vaughan

theorem AnalyticNT.Vaughan.vaughan_weighted_sum (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (s : Finset ℕ) (w : ℕ → ℂ) :
    weightedSum ArithmeticFunction.vonMangoldt s w =
      weightedSum (vaughanLow V) s w + weightedSum (vaughanS1 U) s w -
        weightedSum (vaughanS2 U V) s w + weightedSum (vaughanS3 U V) s w := by sorry
