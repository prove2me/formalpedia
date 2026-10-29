-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_ENNReal_factor_crossmul_real
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_ENNReal_factor_crossmul_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:12:59.210028+00:00
-- url     : https://prove2.me/theorems/96d19d6e-89e1-4df2-8c0f-228cb95d2cdd
-- title:
--   Cross-multiply genuine finite-rate ENNReal moments into a real factor without infinity cancellation
-- statement:
--   Given T=B*K as an ENNReal weighted moment, two positive-rate equations ofReal(a)*T=ofReal(p) and ofReal(b)*B=ofReal(lam), and K=ofReal(L) with L≥0, derive the finite real cross identity L*a=(p/lam)*b. Only positive finite rates are cancelled; no extended-real ∞/∞ division or assertion outside the rate gap.
-- source:
--   Exact algebraic reduction from product identities in ENNReal; ENNReal.ofReal_mul, ofReal_eq_ofReal_iff under nonnegative premises, and real division at positive lam.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_ENNReal_factor_crossmul_real
    (T B K : ENNReal) (a b p lam L : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hlam : 0 < lam) (hL : 0 ≤ L)
    (hFactor : T = B * K)
    (hTerminal : ENNReal.ofReal a * T = ENNReal.ofReal p)
    (hSup : ENNReal.ofReal b * B = ENNReal.ofReal lam)
    (hLap : K = ENNReal.ofReal L) :
    L * a = (p / lam) * b := by sorry
