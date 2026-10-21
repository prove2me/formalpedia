-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_eq_2
-- name    : CLADisclosure.Duopoly.eq_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:42.598337+00:00
-- url     : https://prove2.me/theorems/14810803-ed1b-4163-baf2-6be6599e5045
-- title:
--   Equation (2), p. 12 — expected utility under nondisclosure
-- statement:
--   For the quality distribution $F$ with density $f$, positive gain sensitivity $g$, positive loss sensitivity $l$, and threshold $0<\hat q\le1$, the expected consumer utility of an undisclosed product, before paying its price, is
--
--   $$E(u)+p=\bar q-(l-g)H(\hat q).$$
--
--   The identity shows how the loss-aversion degree $k=l-g$ lowers the product's valuation and therefore enters Bertrand competition.
--
--   **Formalization Note** The price $p$ is omitted from the Lean gross-utility function, so it cancels from the statement.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. 12 (PDF 14), eq. (2); derivation p. A1 (PDF 44)

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- Equation (2), gross of the selling price. -/
theorem eq_2 {F f : ℝ → ℝ} (hF : QualityDist F f)
    {g l qh : ℝ} (hg : 0 < g) (hl : 0 < l)
    (hqh : qh ∈ Set.Ioc (0 : ℝ) 1) :
    nondiscUtility F f g l qh = condMean F f qh - (l - g) * Hfun F qh := by sorry

end CLADisclosure.Duopoly
