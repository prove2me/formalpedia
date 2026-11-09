-- Prove2me | solution 1 for e7_joint_rectangle_factorization
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:53:17.103988+00:00
-- url     : https://prove2.me/submissions/35f5bf59-8036-4e65-9234-6d38a3a8efab

import Mathlib

open MeasureTheory

theorem solution {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ)
    (pastX : Ω → (Fin m → E)) (Xv : Ω → E)
    (R : Set (Fin m → E)) (C : Set E)
    (hXv : Measurable Xv) (hC : MeasurableSet C) :
    P (pastX ⁻¹' R ∩ Xv ⁻¹' C) =
      Measure.map Xv (P.restrict (pastX ⁻¹' R)) C := by
  rw [Measure.map_apply hXv hC, Measure.restrict_apply (hXv hC)]
  rw [Set.inter_comm]
