-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_eq_6
-- name    : CLADisclosure.Duopoly.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:49.657097+00:00
-- url     : https://prove2.me/theorems/1e37620d-8d91-4d5c-89be-1711f5aa96a9
-- title:
--   Equation (6), p. 14 — symmetric disclosure threshold
-- statement:
--   Let gain sensitivity $g$ and disclosure cost $c$ be positive, the loss-aversion degree $k=l-g$ be nonnegative, and $c<G(1)+kH(1)$. A positive threshold $\hat q\le1$ is a symmetric best-response disclosure threshold exactly when the nondisclosure participation bound holds and
--
--   $$F(\hat q)\bigl[G(\hat q)+kH(\hat q)\bigr]=c.$$
--
--   This characterizes an equilibrium of the disclosure game by the paper's implicit threshold equation.
--
--   **Formalization Note** The page explicitly derives the forward implication from indifference. The reverse implication is included to connect an admissible root to the game's best-response equilibrium.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. 14 (PDF 16), eq. (6) and preceding indifference display

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- Equation (6) characterizes the symmetric best-response threshold, p. 14. -/
theorem eq_6 {F f : ℝ → ℝ} (hF : QualityDist F f)
    {g l c qh : ℝ} (hc : 0 < c) (hg : 0 < g) (hk : g ≤ l)
    (hcost : c < Gfun F 1 + (l - g) * Hfun F 1) :
    IsSymEqThreshold F f g l c qh ↔
      qh ∈ Set.Ioc (0 : ℝ) 1 ∧
        0 ≤ nondiscUtility F f g l qh ∧
        F qh * (Gfun F qh + (l - g) * Hfun F qh) = c := by sorry

end CLADisclosure.Duopoly
