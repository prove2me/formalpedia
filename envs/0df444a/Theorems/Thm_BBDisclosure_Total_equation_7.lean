-- Prove2me | Theorems.Thm_BBDisclosure_Total_equation_7
-- name    : BBDisclosure.Total.equation_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:20.317144+00:00
-- url     : https://prove2.me/theorems/8437e3f2-6eb1-46b9-a6b8-0b5890e482c8
-- title:
--   (7), p. 8517 — uniform disclosure, region 1: the first-period share $x_1=\tfrac12+3(p_{b1}-p_{a1})/8$
-- statement:
--   Fix a unit disclosure cost $0<c<5/36$ and a selection of second-period profiles under uniform disclosure, one for each share. Let $p_{a1},p_{b1}\ge0$ be first-period prices and let $x_1\in(0,1)$ be a share consistent with them in the sense of (6), where the profile selected at $x_1$ is a second-period equilibrium whose support lies in region 1 ($\tfrac12-\hat q_b/8<x_1<\tfrac12+\hat q_a/8$). Then
--
--   $$x_1=\frac12+\frac{3(p_{b1}-p_{a1})}{8}.$$
--
--   This is the demand system of the first period: it is the share firms take as given when they choose first-period prices.
--
--   **Formalization Note.** Only the profile selected at $x_1$ itself is required to be an equilibrium; "in region 1" is read as the support condition above. $0<c<5/36$ is the standing assumption (p. 8515).
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, pp. 8516–8517, (6) and (7)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDisclosure.Total

/-- (7), p. 8517: under uniform disclosure, in region 1, the first-period share consistent with (6)
is `x1 = 1/2 + 3(pb1 − pa1)/8`. -/
theorem equation_7 (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (stage2 : ℝ → BBDisclosure.Stage2.ProfileU)
    (pa1 pb1 x1 : ℝ) (hpa : 0 ≤ pa1) (hpb : 0 ≤ pb1) (hx0 : 0 < x1) (hx1 : x1 < 1)
    (heq : BBDisclosure.Stage2.IsStage2EqU c x1 (stage2 x1)) (hreg : BBDisclosure.Stage2.SupportRegion1U x1 (stage2 x1))
    (hshare : IsShareU stage2 pa1 pb1 x1) :
    x1 = 1 / 2 + 3 * (pb1 - pa1) / 8 := by sorry

end BBDisclosure.Total
