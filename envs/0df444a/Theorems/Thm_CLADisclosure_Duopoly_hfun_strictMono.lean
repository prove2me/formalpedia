-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_hfun_strictMono
-- name    : CLADisclosure.Duopoly.hfun_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:49.66481+00:00
-- url     : https://prove2.me/theorems/147dc5c7-fcb2-4e90-9dc9-ce766afba80c
-- title:
--   Proof of Claim 1, p. A2 — derivative and strict growth of H
-- statement:
--   Suppose the density $f$ is continuous and positive on $[0,1]$ and $G$ is strictly increasing on $(0,1]$. For $0<x<1$,
--
--   $$H'(x)=\frac{f(x)F(x-G(x))}{F(x)^2}\bigl(G(x)-G(x-G(x))\bigr).$$
--
--   Consequently $H$ is strictly increasing and positive on $(0,1]$. Its positivity makes a larger loss penalty increase the disclosure incentive at every positive threshold.
--
--   **Formalization Note** The paper states $H'(x)>0$ and $H(1)>0$; positivity at every positive $x$ is included to expose the fact used in the comparative-statics argument.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. A2 (PDF 45), proof of Claim 1, H′(x) display

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- The derivative and monotonicity of H in the proof of Claim 1, p. A2. -/
theorem hfun_strictMono {F f : ℝ → ℝ} (hF : QualityDist F f)
    (hG : StrictMonoOn (Gfun F) (Set.Ioc (0 : ℝ) 1)) :
    (∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (Hfun F)
        (f x * F (x - Gfun F x) / (F x) ^ 2 *
          (Gfun F x - Gfun F (x - Gfun F x))) x) ∧
    StrictMonoOn (Hfun F) (Set.Ioc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Ioc (0 : ℝ) 1, 0 < Hfun F x) := by sorry

end CLADisclosure.Duopoly
