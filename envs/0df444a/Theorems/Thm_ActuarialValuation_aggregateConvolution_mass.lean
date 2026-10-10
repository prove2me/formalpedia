-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateConvolution_mass
-- name    : ActuarialValuation.aggregateConvolution_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:33:52.906011+00:00
-- url     : https://prove2.me/theorems/64a3e081-52fc-4db5-8d74-6d2a814d2c9e
-- title:
--   Finite-support convolution preserves total mass multiplicatively
-- statement:
--   With the first distribution supported no higher than B and the second no higher than C, every pair of possible component losses appears exactly once within the aggregate bound B+C. The double finite sum factors into their respective total probability masses.
--
--   **Mathematical statement**
--
--   $$
--   M_{B+C}(f*g)=M_B(f)M_C(g)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateFiniteMass
import Definitions.Def_actuarial_aggregateConvolution

namespace ActuarialValuation

theorem aggregateConvolution_mass (f g : ℕ → ℝ) (B C : ℕ)
  (hf : ∀ k, B < k → f k = 0)
  (hg : ∀ k, C < k → g k = 0) :
  aggregateFiniteMass (aggregateConvolution f g) (B + C) =
    aggregateFiniteMass f B * aggregateFiniteMass g C := by sorry

end ActuarialValuation
