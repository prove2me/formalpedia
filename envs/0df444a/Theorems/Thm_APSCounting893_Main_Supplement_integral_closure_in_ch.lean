-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_integral_closure_in_ch
-- name    : APSCounting893.Main.Supplement.integral_closure_in_ch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:08:24.133609+00:00
-- url     : https://prove2.me/theorems/f280e14d-ffef-408a-ad8a-7fd54267b490
-- title:
--   Theorem 1.8 — Integral closure membership in CH and non-integrality reduction
-- statement:
--   For valid circuit or sparse inputs over the encoded rational, number or finite fields, let $f$ be the first output, let $F=(f_1,\ldots,f_m)$ be the remaining outputs, and let $A=k[f_1,\ldots,f_m]$. Integral-closure membership has a single fixed-level Counting Hierarchy decider, and non-integrality admits a deterministic polynomial-time many-one reduction to APS:
--
--   $$\mathrm{ICM}\in\mathrm{CH},\qquad\mathrm{non\text{-}ICM}\le_m^{\mathrm P}\mathrm{APS}.$$
--
--   The decider and reduction work uniformly over all valid inputs, including division gates with the published promises and sparse lists with binary exponents. Integrality is over the described base field and APS over its algebraic closure. There is no restriction on expanded degree, characteristic or separability. This supplies the paper's integral-closure complexity conclusion alongside the referenced APS goal.
--
--   Differences from the source:
--   - encoding: binary circuit and sparse instances and their promises → a common SystemInput wrapper, with f first and valid-source many-one correctness; reason: representation tags, field descriptions and all bit lengths remain charged; invalid inputs impose no correctness requirement
--   - encoding: membership belongs to CH → existence of a total language in CH agreeing on every valid integral instance; reason: one language, level, machine and polynomial bound precede every input; no particular CH level is asserted
--   - encoding: Problem 1.2 uses the complex subalgebra on rational input, and Remark 1.9 uses the base field → integrality over the presented base-field subalgebra for all encoded families; reason: integral dependence of these polynomials descends and ascends under scalar extension, so rational inputs give the same decisions
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 1.8, p. 4

import Definitions.Def_APSCounting893_Main_Supplement_DecisionProblems

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Theorem 1.8, including binary sparse inputs, division promises and Remarks 1.9/7.10.
The language, level, machines and polynomial bounds precede every field and input. -/
theorem integral_closure_in_ch :
    (∃ L : Language, InCountingHierarchy L ∧
      ∀ I : SystemInput, I.ValidIntegral → (L I.encode ↔ I.Integral)) ∧
    PolynomialManyOne SystemInput.ValidIntegral (fun I => ¬ I.Integral)
      SystemInput.Valid SystemInput.APS := by sorry

end APSCounting893.Main.Supplement
