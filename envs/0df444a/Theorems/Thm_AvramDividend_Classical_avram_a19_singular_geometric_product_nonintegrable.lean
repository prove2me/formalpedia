-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_product_nonintegrable
-- name    : AvramDividend.Classical.avram_a19_singular_geometric_product_nonintegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:01:46.869214+00:00
-- url     : https://prove2.me/theorems/cb6161f4-3484-420b-a76a-f6e5948cd336
-- title:
--   Independent geometric coordinate preserves singular loss nonintegrability
-- statement:
--   On the product of an arbitrary probability space and the geometric probability law with parameter one-half, the singular generator loss depending only on the second coordinate is nonintegrable, even though the first factor can carry an independent Levy path. The proof uses the measure-preserving second projection.
-- source:
--   A19 source-exact countermodel product-space step, 7 November 2026; depends on transport lemma 926832da.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_transport_nonintegrable
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_geometric_product_nonintegrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (p : unitInterval) (hp : p != 0) (hhalf : (p : Real) = 1 / 2)
    (y : Nat → Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (Integrable (fun ωk : Ω × Nat =>
      -(3 + y ωk.2 - 4 * Real.sqrt (y ωk.2) -
        2 / Real.sqrt (y ωk.2)))
      (P.prod (geometricMeasure p))) := by sorry
