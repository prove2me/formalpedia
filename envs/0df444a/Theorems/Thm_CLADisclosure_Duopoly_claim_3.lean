-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_claim_3
-- name    : CLADisclosure.Duopoly.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:45.454379+00:00
-- url     : https://prove2.me/theorems/7862283c-1dd4-45b9-9ed5-4a3026a1fc88
-- title:
--   Claim 3, p. A6 — unique solution of the duopoly threshold equation
-- statement:
--   Under the paper's continuous positive quality density and strictly increasing $G$, take $g>0$ and $k=l-g\ge0$ and $0<c<G(1)+kH(1)$. There is exactly one $\hat q\in(0,1]$ satisfying
--
--   $$F(\hat q)\bigl[G(\hat q)+kH(\hat q)\bigr]=c.$$
--
--   This gives existence and uniqueness for the equation used to determine the symmetric disclosure threshold.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. A6 (PDF 49), Claim 3; proof continues p. A7 (PDF 50)

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- Claim 3, p. A6: the duopoly threshold equation has a unique solution. -/
theorem claim_3 {F f : ℝ → ℝ} (hF : QualityDist F f)
    (hG : StrictMonoOn (Gfun F) (Set.Ioc (0 : ℝ) 1))
    {g l c : ℝ} (hc : 0 < c) (hg : 0 < g) (hk : g ≤ l)
    (hcost : c < Gfun F 1 + (l - g) * Hfun F 1) :
    ∃! qh : ℝ, qh ∈ Set.Ioc (0 : ℝ) 1 ∧
      F qh * (Gfun F qh + (l - g) * Hfun F qh) = c := by sorry

end CLADisclosure.Duopoly
