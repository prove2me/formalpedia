-- Prove2me | Theorems.Thm_APSCounting893_Main_image_dimension_in_ch
-- name    : APSCounting893.Main.image_dimension_in_ch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:27:34.774181+00:00
-- url     : https://prove2.me/theorems/242225f4-3c43-4de1-9569-1d8d799ce14b
-- title:
--   Lemma 6.1 — Image dimension from exact feasibility
-- statement:
--   Let a rational arithmetic circuit represent a polynomial map $F:\mathbb C^n\to\mathbb C^m$, with every binary constant and wire charged in the input length. There are one language $A\in\mathrm{CH}$ and one deterministic polynomial-time oracle machine computing a function $h$ such that every valid circuit input satisfies
--
--   $$h(\operatorname{enc}(F))=\operatorname{enc}(\dim\overline{F(\mathbb C^n)}).$$
--
--   The oracle, machine and polynomial bound are fixed for all circuits and dimensions, including constant maps. This provides the actual geometric dimension as a function output.
--
--   Differences from the source:
--   - encoding: dimension computable in deterministic polynomial time with a fixed-level CH oracle → one total bit-string function implemented by the finite oracle machine, returning the binary natural dimension; reason: fixes the source Turing model and includes the semantic circuit promise
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 6.1, p. 23, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_SampledResultant

set_option autoImplicit false

namespace APSCounting893.Main

theorem image_dimension_in_ch :
    ∃ (A : Language) (f : Word → Word), InCountingHierarchy A ∧ FunctionInPWithOracle A f ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n), ValidCircuit .rational C →
        ∃ r : ℕ,
          RSCapacity.algDim (imageClosure (rationalComplexPolynomials C)) =
            ((r : ℕ∞) : WithBot ℕ∞) ∧ f C.encode = encodeNat r := by sorry

end APSCounting893.Main
