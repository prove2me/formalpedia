-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
-- name    : AvramDividend.Classical.scaleDeriv_pos
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T23:38:46.515747+00:00
-- url     : https://prove2.me/theorems/4052a131-7dd0-410a-beea-24c391226b00
-- title:
--   The derivative of the q-scale function is positive on the positive half-line
-- statement:
--   For q>0 under the standing assumptions, the q-scale function has strictly positive derivative at every positive point. This is the denominator-positivity input needed for the barrier-value derivative formula.
-- source:
--   Kuznetsov, Kyprianou, Rivero, The theory of scale functions for spectrally negative Lévy processes, relation W^(q)(x)=exp(Phi(q)x) W_Phi(q)(x), strict increase of scale functions, and Phi(q)>0 for q>0; combined with C1 regularity under condition (3.3).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_pos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by sorry

end AvramDividend.Classical
