-- Prove2me | solution 1 for flt5_cyclotomic5_irred
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-13T12:33:41.446242+00:00
-- url     : https://prove2.me/submissions/fc64e0c3-7b25-4635-9444-dfa4554c518f

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Data.Int.Basic

noncomputable section

-- cyclotomic.irreducible_rat is in Mathlib.RingTheory.Polynomial.Cyclotomic.Roots,
-- which is transitively imported by PrimitiveRoots.

theorem solution : Irreducible (Polynomial.cyclotomic 5 ℚ) :=
  Polynomial.cyclotomic.irreducible_rat (by decide)

end
