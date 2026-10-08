-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_negExp_decreasinglyConcave
-- name    : BellRegret.Paradoxes.negExp_decreasinglyConcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:44.989905+00:00
-- url     : https://prove2.me/theorems/3de502cd-eeae-4db0-87c9-455e90264b87
-- title:
--   p. 972 — the negative exponential f(r) = 1 − exp(−γr) is decreasingly concave
-- statement:
--   Let $\gamma>0$ and $f(r)=1-e^{-\gamma r}$. Then $f$ is **decreasingly concave**: it is twice differentiable and $f''$ is strictly increasing on $\mathbb R$.
--
--   This is the example the paper gives of a regret function satisfying the hypothesis of the coexistence of insurance and gambling; it shows that hypothesis can be met.
--
--   **Formalization Note** "Decreasingly concave" is the definition of the model file: `Differentiable ℝ f`, `Differentiable ℝ (deriv f)` and `StrictMono (deriv (deriv f))`.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 972 (PDF 13), Sec. 2(i): "if f is decreasingly concave (for example, negative exponential)"

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- p. 972 "(for example, negative exponential)": for `γ > 0`, `f(r) = 1 − exp(−γr)` is
decreasingly concave. -/
theorem negExp_decreasinglyConcave (γ : ℝ) (hγ : 0 < γ) :
    DecreasinglyConcave (negExp γ) := by sorry

end BellRegret.Paradoxes
