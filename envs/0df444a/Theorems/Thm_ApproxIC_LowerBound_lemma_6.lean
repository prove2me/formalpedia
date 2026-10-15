-- Prove2me | Theorems.Thm_ApproxIC_LowerBound_lemma_6
-- name    : ApproxIC.LowerBound.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:23.429167+00:00
-- url     : https://prove2.me/theorems/d5ea4a32-5350-4021-9457-f9623c1adc31
-- title:
--   Lemma 6, p. 60 — 2(t+1)e^{−1}e^{−t} < Γ(t) ≤ 2(t+2)e^{−(t+1)} for t ≥ 0
-- statement:
--   For $t\ge 0$ let
--   $$\Gamma(t)=\sum_{j=0}^{\lfloor t\rfloor+1}\frac{(-1)^je^{-j}}{j!}\,(t+1-j)^j.$$
--   Then for every $t\ge0$,
--   $$2(t+1)e^{-1}e^{-t}<\Gamma(t)\le 2(t+2)e^{-(t+1)}.$$
--
--   $\Gamma(2\delta/\mu)$ is the value at $p^\star+\delta$ of the rescaled solution of the delay equation, so these bounds locate the delay $\delta$ for which the perturbed delayed allocation reaches $1$ (Proposition 5).
--
--   **Formalization Note** Powers are natural-number powers and $\lfloor t\rfloor$ is the natural floor; at $j=\lfloor t\rfloor+1$ the base $t+1-j$ lies in $[0,1)$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 60, Appendix C.1, Lemma 6

import Mathlib
import Definitions.Def_ApproxIC_LowerBound_Delayed

namespace ApproxIC.LowerBound

/-- Lemma 6 (Appendix C.1, p. 60): `2(t + 1)e^{−1}e^{−t} < Γ(t) ≤ 2(t + 2)e^{−(t+1)}` for all `t ≥ 0`. -/
theorem lemma_6 (t : ℝ) (ht : 0 ≤ t) :
    2 * (t + 1) * Real.exp (-1) * Real.exp (-t) < Gamma t ∧
      Gamma t ≤ 2 * (t + 2) * Real.exp (-(t + 1)) := by sorry

end ApproxIC.LowerBound
