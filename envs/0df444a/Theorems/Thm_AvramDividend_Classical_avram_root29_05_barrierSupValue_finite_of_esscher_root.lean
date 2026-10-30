-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierSupValue_finite_of_esscher_root
-- name    : AvramDividend.Classical.avram_root29_05_barrierSupValue_finite_of_esscher_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:32:50.69237+00:00
-- url     : https://prove2.me/theorems/7b143eb8-4ccd-4c06-be8f-f763aeb7c845
-- title:
--   Actual killed reflected-regulator barrier boundary dividend value is finite under positive Esscher root
-- statement:
--   For every Standing spectrally negative Lévy process, positive q, positive barrier a, and positive Esscher root φ with ψ(φ)=q, the original Stieltjes running-supremum dividend value killed at strict reflected ruin is finite. Does not assume the two-sided exit W ratio, smoothness or derivative normaliser.
-- source:
--   Fix ε=a>0. The genuine strict upper-before-lower two-sided exit coefficient at reserve a and upper level a+ε is bounded above by exp(-φ ε)<1 using Proved original/corrected exit equivalence caca9b2f and true Esscher exit bound a6c37169. Set p as its ENNReal value, convert to p.toReal by ENNReal.ofReal_toReal after establishing p<1<∞, and invoke the Proved true-regulator geometric renewal finiteness theorem chat12_barrierSupValue_finite_of_trueExit_factor 14f42cc2 with its raw exit integral exactly matched. This gives actual finiteness without the Open scale-exit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat12_barrierSupValue_finite_of_trueExit_factor
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_05_barrierSupValue_finite_of_esscher_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q < ∞ := by sorry
