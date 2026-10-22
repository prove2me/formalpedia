-- Prove2me | Theorems.Thm_DiscServLine_SPT_root_A35_exists
-- name    : DiscServLine.SPT.root_A35_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:26.563386+00:00
-- url     : https://prove2.me/theorems/b14381e1-0160-4d6d-a86b-414c81d4f3c9
-- title:
--   Proof of Proposition 5 (i), p. 43 (PDF 43) — (A–35) has a root ω ∈ (0, 1)
-- statement:
--   Assume $0<c<\bar\theta$, $b>0$ and $\Lambda>0$, and let $F$ be the left-hand side of equation (A–35), with $\kappa=2b/(\Lambda c)$:
--   $$F(\omega)=\tfrac12\ln\frac{\frac{b}{\Lambda c}+\frac1\omega+\frac{1}{\sqrt\omega}\sqrt{\frac1\omega+\kappa}}{\frac{b}{\Lambda c}+1+\sqrt{1+\kappa}}-\frac{\bar\theta/c-1}{\sqrt{\frac1\omega+\kappa}}+\sqrt{1+\kappa}-\sqrt{1+\kappa\omega}.$$
--   Then there is $\omega\in(0,1)$ with
--   $$F(\omega)=0 .$$
--
--   The root $\omega=\underline w/\bar w$ parametrises the optimal SPT service line of Lemma A7, and $\omega<1$ is equivalent to $\underline t<\bar t$.
--
--   **Formalization Note** Uniqueness of the root is not claimed (the paper does not state it).
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 43 (PDF 43), proof of Proposition 5 (i); (A–35) at Supplementary Document, p. 22 (PDF 69)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem root_A35_exists (P : Params) (hP : P.Standing) :
    ∃ ω ∈ Set.Ioo (0 : ℝ) 1, F35 P ω = 0 := by sorry

end DiscServLine.SPT
