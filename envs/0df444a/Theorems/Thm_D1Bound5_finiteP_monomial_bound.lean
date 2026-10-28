-- Prove2me | Theorems.Thm_D1Bound5_finiteP_monomial_bound
-- name    : D1Bound5.finiteP_monomial_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:41.981425+00:00
-- url     : https://prove2.me/theorems/550bd9bd-eca6-44d3-b786-826b8dedc0cb
-- title:
--   Finite P monomial bound
-- statement:
--   A common scalar bound for both the leading and tail terms of P. The exponent condition records exactly how much reciprocal-anchor decay remains after allowing two powers of the largest anchor.
-- source:
--   D1Bound5/FinitePMonomial.lean, lines 8-42, SHA-256 2cdd205c10074edc08dfd393515a0eb70dfdf8436260ab250c4bad687559c5be. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

section
namespace D1Bound5


theorem _root_.D1Bound5.finiteP_monomial_bound (A S U V : ℝ) (q n d e : ℕ)
    (hA1 : 1 ≤ A) (hAU : A ≤ U) (hAV : A ≤ V)
    (hUS : U ≤ S) (hVS : V ≤ S) (he : e ≤ 2)
    (hsum : d+e+q ≤ n+2) :
    U^d*V^e/U^n ≤ S^2/A^q := by sorry

end D1Bound5
end
