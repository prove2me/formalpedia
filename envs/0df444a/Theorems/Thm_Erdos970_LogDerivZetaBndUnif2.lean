-- Prove2me | Theorems.Thm_Erdos970_LogDerivZetaBndUnif2
-- name    : Erdos970.LogDerivZetaBndUnif2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:25.921989+00:00
-- url     : https://prove2.me/theorems/8fc21583-d8c9-4eca-b0aa-f0215413b94e
-- title:
--   Uniform bound |ζ′/ζ(σ+it)| ≤ C log²|t| to the right of a zero-free region
-- statement:
--   There are constants $A\in(0,1/2]$ and $C>0$ such that for all real $\sigma,t$ with $|t|>3$ and $\sigma\ge 1-A/\log|t|$,
--
--   $$\Big|\frac{\zeta'(\sigma+it)}{\zeta(\sigma+it)}\Big|\le C\,(\log|t|)^2 .$$
--
--   Here $\zeta$ is Mathlib's `riemannZeta`, $\zeta'$ its complex derivative, and division by zero is $0$ (the statement does not itself assert $\zeta(\sigma+it)\ne0$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.LogDerivZetaBndUnif2`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace Erdos970

open _root_.Set
open _root_.Function
open _root_.Filter
open _root_.Complex
open _root_.Real

theorem LogDerivZetaBndUnif2 :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 1)), ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      C * Real.log |t| ^ 2 := by
  sorry

end Erdos970
