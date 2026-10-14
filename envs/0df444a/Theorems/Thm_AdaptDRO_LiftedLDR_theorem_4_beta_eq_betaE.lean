-- Prove2me | Theorems.Thm_AdaptDRO_LiftedLDR_theorem_4_beta_eq_betaE
-- name    : AdaptDRO.LiftedLDR.theorem_4_beta_eq_betaE
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:28.835664+00:00
-- url     : https://prove2.me/theorems/3611988c-b103-4263-815a-45d44cdfcdfc
-- title:
--   Theorem 4 — exact lifted linear decision rules with one recourse variable
-- statement:
--   Suppose the second-stage problem has **complete recourse** and exactly one free second-stage decision variable. For the SOC ambiguity set of Definition 3 and its lifted ambiguity set, the worst-case expected optimal recourse cost equals the best worst-case expected cost among rules affine in the primary and auxiliary random variables. For every first-stage decision $x$,
--
--   $$
--   \beta(x)=\beta_E(x).
--   $$
--
--   Thus the extended affine decision-rule approximation is exact in this recourse regime, even though regular affine rules need not be feasible or exact.
--
--   **Formalization Note** The statement makes Assumption 1 and dual feasibility explicit. Theorem 4 does not repeat Assumption 1, but its route through Theorem 1 uses it; primal feasibility alone does not imply dual feasibility. The four model values use extended-real suprema and infima, while finite first moments in the ambiguity sets ensure that affine expectations are real.
-- source:
--   Bertsimas, Sim, Zhang, Adaptive distributionally robust optimization, Management Science 65(2) (2019), p. 610, Theorem 4; p. 608, Assumption 1 and Remarks after Theorem 1

import Mathlib
import Definitions.Def_AdaptDRO_LiftedLDR_Model

namespace AdaptDRO.LiftedLDR

/-- Theorem 4 (p. 610): with one free recourse variable and complete
recourse, the lifted affine rule has the exact worst-case value. -/
theorem theorem_4_beta_eq_betaE
    {I1 I2 I3 L1 L2 M N1 : ℕ} (m : Model I1 I2 L1 M N1 1)
    (C : Matrix (Fin L2) (Fin I1) ℝ)
    (D : Matrix (Fin L2) (Fin I2) ℝ)
    (E : Matrix (Fin L2) (Fin I3) ℝ)
    (h : Fin L2 → ℝ) (K : Set (Fin L2 → ℝ))
    (hSOC : m.SOCData) (hAssumption1 : m.Assumption1 C D E h K)
    (hrec : m.recourse.Complete) (hdual : m.recourse.DualFeasible) :
    ∀ x : Fin N1 → ℝ, m.beta x = m.betaE x := by sorry

end AdaptDRO.LiftedLDR
