-- Prove2me | Theorems.Thm_FaulhuberTFA_ambiguity_box
-- name    : FaulhuberTFA.ambiguity_box
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:49:06.78387+00:00
-- url     : https://prove2.me/theorems/8d14abd5-313f-4c8c-969c-36e4d814dc47
-- title:
--   Example 3.4(a) and Remark: the ambiguity function of the box function
-- statement:
--   Let $b_0=\chi_{[-1/2,1/2]}$ be the box function on $\mathbb{R}$. For $x,\omega\in\mathbb{R}$,
--
--   $$Ab_0(x,\omega)=\begin{cases}\dfrac{\sin(\pi\omega(1-|x|))}{\pi\omega}, & |x|\le1,\ \omega\neq0,\\[4pt] 1-|x|, & |x|\le1,\ \omega=0,\\[2pt] 0, & |x|>1.\end{cases}$$
--
--   The value at $\omega=0$ is the limit computed in the Remark after Example 3.4; the formula of Example 3.4(a) is undefined there.
--
--   **Formalization Note** $\mathbb{R}$ is represented as $\mathbb{R}^1$, a point being identified with its single coordinate.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, Example 3.4(a), p. 27, and the Remark on p. 28 for the value at $\omega = 0$

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem ambiguity_box (x ω : Rd 1) :
    ambiguity box0 x ω =
      if |x 0| ≤ 1 then
        (if ω 0 = 0 then ((1 - |x 0| : ℝ) : ℂ)
         else ((Real.sin (Real.pi * ω 0 * (1 - |x 0|)) / (Real.pi * ω 0) : ℝ) : ℂ))
      else 0 := by sorry

end FaulhuberTFA
