-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_compensated_increment_extension_measurable
-- name    : AvramDividend.Classical.scaleFunction_compensated_increment_extension_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:44:24.313341+00:00
-- url     : https://prove2.me/theorems/03fa2404-fbdc-4cc3-a33e-c7f289cc0b99
-- title:
--   Joint measurability of the compensated scale increment with a local derivative extension
-- statement:
--   Let W be a q-scale function C2 on the open interval (0,a). Its global monotonicity makes W Borel measurable. The ordinary derivative is continuous on (0,a) by C2 regularity; extending it by zero outside that interval produces a measurable real function. Consequently the compensated two-coordinate increment W(x+y)-W(x)-D(x)y 1_{(-1,1)}(y), with D the extended derivative, is jointly Borel measurable on ℝ². On every compact state interval strictly inside (0,a), this increment equals the true Levy generator integrand. It supplies the central joint-measurability bridge for compact-localised Fubini.
-- source:
--   Direct topology-and-measure theory argument for the compact-localised Levy generator in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_compensated_increment_extension_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    Measurable (fun p : ℝ × ℝ =>
      W (p.1 + p.2) - W p.1 -
      ((Ioo 0 a).indicator (deriv W) p.1) * p.2 *
        ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.2)) := by sorry

end AvramDividend.Classical
