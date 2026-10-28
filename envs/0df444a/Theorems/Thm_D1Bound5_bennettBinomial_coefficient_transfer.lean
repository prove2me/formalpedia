-- Prove2me | Theorems.Thm_D1Bound5_bennettBinomial_coefficient_transfer
-- name    : D1Bound5.bennettBinomial_coefficient_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:20.557993+00:00
-- url     : https://prove2.me/theorems/63247c1b-d649-4127-b028-fffdf280af56
-- title:
--   Bennett Binomial coefficient transfer
-- statement:
--   The one-term binomial identity transferring a coefficient in the residual variable to a local residue coefficient. It holds for every exponent parameter, including those shifted to negative values in the node-removal induction.
-- source:
--   D1Bound5/BennettBinomialTransfer.lean, lines 20-58, SHA-256 7c8a669a4f1cc287328c81f5b671e332dd23a6d5cc77c366017077852274896c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]




theorem _root_.D1Bound5.bennettBinomial_coefficient_transfer (k h r : ℕ) (hhk : h ≤ k) (ν a : F) :
    Ring.choose ((k : F) + ν) h *
      PowerSeries.coeff r
        (((PowerSeries.X : PowerSeries F) ^ h *
          (1 + PowerSeries.C a * PowerSeries.X) ^ (k - h)) *
            PowerSeries.rescale a (PowerSeries.binomialSeries F ν)) =
      Ring.choose ((k : F) + ν) r *
        PowerSeries.coeff h ((PowerSeries.C a + PowerSeries.X : PowerSeries F) ^ r) := by sorry

end D1Bound5
end
