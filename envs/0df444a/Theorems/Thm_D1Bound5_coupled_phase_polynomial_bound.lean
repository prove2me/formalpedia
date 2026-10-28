-- Prove2me | Theorems.Thm_D1Bound5_coupled_phase_polynomial_bound
-- name    : D1Bound5.coupled_phase_polynomial_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:53.477501+00:00
-- url     : https://prove2.me/theorems/55978b27-2c20-42fc-a18a-4b51eb997a48
-- title:
--   Coupled phase polynomial bound
-- statement:
--   Exact rational brackets around the positive critical point suffice for a global bound. The two outer intervals use the proved derivative sign; the middle interval uses monotonicity of its two positive factors.
-- source:
--   D1Bound5/CoupledPhaseBounds.lean, lines 36-106, SHA-256 14ad3644c7d0af80f0ec212461e5adea70bec57470ae7e0a8a0ee48d46ce9bc9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions

section
namespace D1Bound5









theorem _root_.D1Bound5.coupled_phase_polynomial_bound (q l r F : ℝ)
    (hq : 1 ≤ q) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 2)
    (hleft : phaseCritical q l ≤ 0) (hright : 0 ≤ phaseCritical q r)
    (henvelope : (4-l^2)^4*(1+(1/q)^2+r/q)^2 < F)
    (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) : coupledPhasePolynomial q x < F := by sorry







end D1Bound5
end
