-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_negExp_conditions
-- name    : BellRegret.Paradoxes.negExp_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:24.230715+00:00
-- url     : https://prove2.me/theorems/1cbaa6bb-4052-47af-9e40-214236c29c02
-- title:
--   p. 978 — f(r) = 1 − exp(−γr): f concave, g convex (r ≥ 0), g(r)/r increasing for r > 0
-- statement:
--   Let $\gamma>0$, let $f(r)=1-e^{-\gamma r}$ and $g(r)=r+f(r)-f(-r)$. Then
--   1. $f$ is concave on $\mathbb R$;
--   2. $g$ is convex on $[0,\infty)$;
--   3. $r\mapsto g(r)/r$ is strictly increasing on $(0,\infty)$.
--
--   These are the three conditions under which Section 3 says the decision maker behaves consistently with the paradoxes of Section 2, so the negative exponential is a concrete regret function realising all of them.
--
--   **Formalization Note** The page states (ii) "$g(r)$ is convex" without a domain. Here $g(r)=r+2\sinh(\gamma r)$, which is concave for $r<0$ (as the page itself notes on p. 977: "g would be concave for negative x"), so (ii) is stated on $r\ge0$. "Increasing" in (iii) is read strictly.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 978 (PDF 19), Sec. 3, "The case f(r) = 1 − exp(−γr), for γ > 0, satisfies …"; g from p. 976 (PDF 17)

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- p. 978: for `γ > 0`, `f(r) = 1 − exp(−γr)` satisfies (i) `f` is concave, (ii) `g(r) =
r + f(r) − f(−r)` is convex (read on `r ≥ 0`), and (iii) `g(r)/r` is increasing for positive
`r`. -/
theorem negExp_conditions (γ : ℝ) (hγ : 0 < γ) :
    ConcaveOn ℝ Set.univ (negExp γ) ∧
    ConvexOn ℝ (Set.Ici 0) (regretG (negExp γ)) ∧
    StrictMonoOn (fun r => regretG (negExp γ) r / r) (Set.Ioi 0) := by sorry

end BellRegret.Paradoxes
