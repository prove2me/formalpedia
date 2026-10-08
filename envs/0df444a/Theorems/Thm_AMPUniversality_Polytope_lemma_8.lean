-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_lemma_8
-- name    : AMPUniversality.Polytope.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:38.966382+00:00
-- url     : https://prove2.me/theorems/8d647f68-db79-4304-832e-2a1157a70215
-- title:
--   Lemma 8, p. 60 — strict convexity and the unique minimum of Gε
-- statement:
--   Fix $\varepsilon\in(0,1)$ and let $G_\varepsilon$ be the Gaussian expectation in (C.3). It is strictly convex on $[0,\infty)$, has a unique minimizer $\alpha_*(\varepsilon)>0$, satisfies $G_\varepsilon(0)=1$, and diverges as $\alpha\to\infty$. At the minimizer,
--
--   $$G_\varepsilon(\alpha_*)=\varepsilon+2(1-\varepsilon)\Phi(-\alpha_*)=\tfrac12G_\varepsilon''(\alpha_*)\in(0,1).$$
--
--   This lemma supplies the attained scalar threshold used by Lemma 9. **Formalization Note** Integrability of the Gaussian-square term is an additional conclusion, ensuring its Lean integral has its mathematical value.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 60, Lemma 8 and equations (C.3), (C.6)

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Curve
import Definitions.Def_AMPUniversality_Polytope_GEps

set_option autoImplicit false
open MeasureTheory Filter Set

namespace AMPUniversality.Polytope

/-- Lemma 8, p. 60, including the integrability needed for the Gaussian
expectation in (C.3). -/
theorem lemma_8 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ α : ℝ,
      Integrable (fun z : ℝ => (max (z - α) 0) ^ 2)
        (ProbabilityTheory.gaussianReal 0 1)) ∧
    StrictConvexOn ℝ (Ici 0) (GEps ε) ∧
    GEps ε 0 = 1 ∧
    Tendsto (GEps ε) atTop atTop ∧
    ∃ αstar : ℝ,
      0 < αstar ∧
      (∀ β : ℝ, 0 ≤ β →
        GEps ε αstar ≤ GEps ε β ∧
        (GEps ε β = GEps ε αstar → β = αstar)) ∧
      GEps ε αstar = ε + 2 * (1 - ε) * Phi (-αstar) ∧
      GEps ε αstar = (deriv (deriv (GEps ε)) αstar) / 2 ∧
      0 < GEps ε αstar ∧ GEps ε αstar < 1 := by sorry

end AMPUniversality.Polytope
