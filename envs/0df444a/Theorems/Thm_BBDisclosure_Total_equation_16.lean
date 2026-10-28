-- Prove2me | Theorems.Thm_BBDisclosure_Total_equation_16
-- name    : BBDisclosure.Total.equation_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:15.578339+00:00
-- url     : https://prove2.me/theorems/e7cf049a-81e7-4f4e-a88a-06017b467d30
-- title:
--   (16), p. 8519 — BBD, region 1: the first-period share $x_1=\tfrac12+3(p_{b1}-p_{a1})/8$
-- statement:
--   Fix a unit disclosure cost $0<c<5/36$ and a selection of second-period profiles under behavior-based disclosure, one for each share. Let $p_{a1},p_{b1}\ge0$ and let $x_1\in(0,1)$ be a share consistent with them in the sense of (15), where the profile selected at $x_1$ is a second-period equilibrium whose support lies in region 1 ($\tfrac12-\hat q_{bn}/8<x_1<\tfrac12+\hat q_{an}/8$). Then
--
--   $$x_1=\frac12+\frac{3(p_{b1}-p_{a1})}{8}.$$
--
--   Under BBD the first-period demand system is the same as under uniform disclosure, (7).
--
--   **Formalization Note.** Only the profile selected at $x_1$ is required to be an equilibrium; "in region 1" is read as the support condition above. $0<c<5/36$ is the standing assumption (p. 8515).
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8519, (15) and (16)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDisclosure.Total

/-- (16), p. 8519: under behavior-based disclosure, in region 1, the first-period share consistent
with (15) is `x1 = 1/2 + 3(pb1 − pa1)/8`. -/
theorem equation_16 (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (stage2 : ℝ → BBDisclosure.Stage2.ProfileBBD)
    (pa1 pb1 x1 : ℝ) (hpa : 0 ≤ pa1) (hpb : 0 ≤ pb1) (hx0 : 0 < x1) (hx1 : x1 < 1)
    (heq : BBDisclosure.Stage2.IsStage2EqBBD c x1 (stage2 x1)) (hreg : BBDisclosure.Stage2.SupportRegion1BBD x1 (stage2 x1))
    (hshare : IsShareBBD stage2 pa1 pb1 x1) :
    x1 = 1 / 2 + 3 * (pb1 - pa1) / 8 := by sorry

end BBDisclosure.Total
