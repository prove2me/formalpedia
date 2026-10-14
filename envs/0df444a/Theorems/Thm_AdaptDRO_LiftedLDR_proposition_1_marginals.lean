-- Prove2me | Theorems.Thm_AdaptDRO_LiftedLDR_proposition_1_marginals
-- name    : AdaptDRO.LiftedLDR.proposition_1_marginals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:24.6224+00:00
-- url     : https://prove2.me/theorems/8227ef42-d1a0-48df-9e62-4983d7dacbde
-- title:
--   Proposition 1 — original laws are precisely lifted primary marginals
-- statement:
--   Let $F$ be the SOC ambiguity set of Definition 3, and let $\mathcal G$ be its lifting through the same support $W$, functions $g_i$, and moment data $(G,\mu,\sigma)$. If $P_z$ denotes the primary-coordinate marginal of a joint law $P$, then
--
--   $$
--   F=\{P_z:P\in\mathcal G\}.
--   $$
--
--   This identifies the joint-law formulation with the original moment and support constraints; it is the basis for comparing the two worst-case expectations.
--
--   **Formalization Note** Laws have finite first moments and integrable $g_i$, making each displayed expectation genuine. The functions $g_i$ are measurable and their epigraphs SOC representable, so taking a joint law with $u=g(z)$ is well-defined. This statement also covers empty ambiguity sets.
-- source:
--   Bertsimas, Sim, Zhang, Adaptive distributionally robust optimization, Management Science 65(2) (2019), p. 607, Proposition 1; proof p. 608

import Mathlib
import Definitions.Def_AdaptDRO_LiftedLDR_Model

namespace AdaptDRO.LiftedLDR

open MeasureTheory

/-- Proposition 1 (p. 607): the original ambiguity set is exactly the set of
primary marginals of the lifted ambiguity set. -/
theorem proposition_1_marginals
    {I1 I2 L1 M N1 N2 : ℕ} (m : Model I1 I2 L1 M N1 N2)
    (hSOC : m.SOCData) :
    m.ambF = (fun P : Measure ((Fin I1 → ℝ) × (Fin I2 → ℝ)) =>
      P.map Prod.fst) '' m.liftedAmb := by sorry

end AdaptDRO.LiftedLDR
