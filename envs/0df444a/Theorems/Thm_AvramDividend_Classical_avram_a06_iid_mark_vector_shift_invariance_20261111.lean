-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_iid_mark_vector_shift_invariance_20261111
-- name    : AvramDividend.Classical.avram_a06_iid_mark_vector_shift_invariance_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:12:46.453847+00:00
-- url     : https://prove2.me/theorems/df851227-dbe6-4707-be4f-3e804cbea456
-- title:
--   Finite IID mark vectors have shift-invariant joint law
-- statement:
--   An IID sequence of random marks has the same joint distribution on any k-consecutive-element window as on its initial k elements. This permits block-length-only Fourier factors for random finite mark blocks in the A06 bounded-variation jump verification route.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a06_iid_mark_vector_shift_invariance_20261111
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → A) (hY : ∀ j, Measurable (Y j))
    (hInd : iIndepFun Y P)
    (hSame : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (a k : ℕ) :
    IdentDistrib (fun ω => fun i : Fin k => Y (a + i.val) ω)
      (fun ω => fun i : Fin k => Y i.val ω) P P := by sorry
