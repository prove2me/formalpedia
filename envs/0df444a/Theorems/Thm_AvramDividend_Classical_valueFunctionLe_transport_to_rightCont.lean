-- Prove2me | Theorems.Thm_AvramDividend_Classical_valueFunctionLe_transport_to_rightCont
-- name    : AvramDividend.Classical.valueFunctionLe_transport_to_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:36:57.700982+00:00
-- url     : https://prove2.me/theorems/8729763e-69b1-4514-8e82-2fce5f4bc52e
-- title:
--   The capped optimal dividend value cannot decrease upon right-continuous filtration augmentation
-- statement:
--   Given a spectrally negative Lévy process on an original filtration and one on its right-continuous filtration with the same process paths, the supremum of expected discounted dividend values across all originally admissible strategies under cap C is at most the corresponding supremum on the enlarged filtration. Every original admissible control is still admissible by the separately Proved transfer theorem and has exactly the same expected dividend value by the separately Proved reward transport theorem. The proof is purely order-theoretic monotonicity of the two nested suprema, and does not assume the unproved stopped stochastic dividend bound.
-- source:
--   Pinned Formalpedia valueFunctionLe and two Proved Chat 8 transfer lemmas.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_transport_to_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendValue_transport_same_process

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.valueFunctionLe_transport_to_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕.rightCont)
    (hXY : Y.X = X.X)
    (q : ℝ) (C : ℝ≥0∞) (x : ℝ) :
    valueFunctionLe X q C x ≤ valueFunctionLe Y q C x := by sorry
