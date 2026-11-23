-- Prove2me | Theorems.Thm_BroughanRH_psiSmallPower
-- name    : BroughanRH.psiSmallPower
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:08:35.211804+00:00
-- url     : https://prove2.me/theorems/92362744-aa18-4e87-b04e-55313b7228e5
-- title:
--   The small-power Chebyshev error
-- statement:
--   The Chebyshev error is $O_\varepsilon(x^{1/2+\varepsilon})$ for each positive $\varepsilon$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §4.1. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem psiSmallPower :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun x : ℝ => Chebyshev.psi x - x) (fun x : ℝ => x^(1/2+ε)) := by sorry

end BroughanRH
