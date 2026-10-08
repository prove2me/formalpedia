-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_ratio_strictMono_of_deriv2
-- name    : BellRegret.Paradoxes.ratio_strictMono_of_deriv2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:14.75+00:00
-- url     : https://prove2.me/theorems/3e36ab37-7ef5-4b4d-9d26-5b8ba393c4c0
-- title:
--   p. 972 — f″(x) > f″(−x) for x > 0 makes (f(x) − f(−x))/x increasing
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be differentiable with differentiable derivative, and suppose that
--   $$f''(x)>f''(-x)\qquad\text{for every }x>0.$$
--   Then $x\mapsto (f(x)-f(-x))/x$ is strictly increasing on $(0,\infty)$.
--
--   In particular every decreasingly concave $f$ (one with strictly increasing $f''$) satisfies the sufficient condition of inequalities (5), (6) and (11).
--
--   **Formalization Note** The page writes "$f''(x)>f''(-x)$ for all $x$", which no function satisfies (apply it at $x$ and at $-x$). The formalization reads it for $x>0$, the only consistent reading. Twice differentiability is stated as `Differentiable ℝ f` and `Differentiable ℝ (deriv f)`.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 972 (PDF 13), Sec. 2(i): "This will be the case if, but not only if, f''(x) > f''(−x) for all x"

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- p. 972: `(f(x) − f(−x))/x` is strictly increasing on `x > 0` if `f″(x) > f″(−x)`
(read for every `x > 0`). -/
theorem ratio_strictMono_of_deriv2 (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (h2 : ∀ x : ℝ, 0 < x → deriv (deriv f) (-x) < deriv (deriv f) x) :
    StrictMonoOn (fun x => (f x - f (-x)) / x) (Set.Ioi 0) := by sorry

end BellRegret.Paradoxes
