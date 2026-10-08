-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_display5_of_ratio_strictMono
-- name    : BellRegret.Paradoxes.display5_of_ratio_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:59.825887+00:00
-- url     : https://prove2.me/theorems/5c674031-fb15-42e3-86d2-4828643671a4
-- title:
--   p. 972 — (5) and (6) hold if (f(x) − f(−x))/x is increasing in x
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be such that
--   $$x\mapsto\frac{f(x)-f(-x)}{x}$$
--   is strictly increasing on $(0,\infty)$, and let $0<p<\tfrac12$. Then
--   $$p\,[f(1-p)-f(p-1)]>(1-p)\,[f(p)-f(-p)],$$
--   i.e. inequalities (5) and (6) hold in the direction shown.
--
--   This is the sufficient condition through which decreasing concavity yields both the gamble and the insurance.
--
--   **Formalization Note** "Increasing" is read strictly because (5) is strict. The function $(f(x)-f(-x))/x$ is undefined at $0$ and even, so "increasing in $x$" is read on $x>0$; the statement uses it only at $p$ and $1-p$, both positive.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 972 (PDF 13), Sec. 2(i), the sentence after Table III

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- p. 972: inequalities (5) and (6) hold if `(f(x) − f(−x))/x` is (strictly) increasing
in `x > 0`, for `0 < p < 1/2`. -/
theorem display5_of_ratio_strictMono (f : ℝ → ℝ) (p : ℝ)
    (hf : StrictMonoOn (fun x => (f x - f (-x)) / x) (Set.Ioi 0))
    (hp0 : 0 < p) (hp : p < 1 / 2) :
    p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p)) := by sorry

end BellRegret.Paradoxes
