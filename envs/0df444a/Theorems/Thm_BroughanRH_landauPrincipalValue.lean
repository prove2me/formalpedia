-- Prove2me | Theorems.Thm_BroughanRH_landauPrincipalValue
-- name    : BroughanRH.landauPrincipalValue
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:43.816552+00:00
-- url     : https://prove2.me/theorems/e6f9e084-e272-4701-b01f-f45a948961f5
-- title:
--   Massias–Nicolas–Robin’s permutation-order criterion
-- statement:
--   For all sufficiently large $n$, the maximal permutation order $g(n)$ satisfies $\log g(n)<\sqrt{\operatorname{li}^{-1}(n)}$. The increasing branch of the principal-value logarithmic integral fixes the inverse for large arguments.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.42. https://doi.org/10.1017/9781108178228

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace BroughanRH

theorem landauPrincipalValue :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let inv (y : ℝ) := sInf {x : ℝ | 2 ≤ x ∧ y ≤ li x}
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (LandauFunction.landau n) < Real.sqrt (inv n) := by sorry

end BroughanRH
