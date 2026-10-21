-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_condMean_eq
-- name    : CLADisclosure.Duopoly.condMean_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:43.525507+00:00
-- url     : https://prove2.me/theorems/f8b6a89d-2e1a-4ad6-9fa6-660b4210f97f
-- title:
--   p. 12 — conditional mean of undisclosed quality
-- statement:
--   Let $F$ have a continuous positive density $f$ on $[0,1]$, and let $0<\hat q\le1$. The mean quality inferred from nondisclosure satisfies
--
--   $$\bar q=E[q\mid q\le\hat q]=\hat q-G(\hat q).$$
--
--   This identity expresses consumers' updated belief in terms of the normalized CDF integral used throughout the paper.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. 12 (PDF 14), nondisclosure-belief display

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- Nondisclosure belief on p. 12. -/
theorem condMean_eq {F f : ℝ → ℝ} (hF : QualityDist F f)
    {qh : ℝ} (hqh : qh ∈ Set.Ioc (0 : ℝ) 1) :
    condMean F f qh = qh - Gfun F qh := by sorry

end CLADisclosure.Duopoly
