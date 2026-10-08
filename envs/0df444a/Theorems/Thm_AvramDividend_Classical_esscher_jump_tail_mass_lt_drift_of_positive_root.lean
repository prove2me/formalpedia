-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_jump_tail_mass_lt_drift_of_positive_root
-- name    : AvramDividend.Classical.esscher_jump_tail_mass_lt_drift_of_positive_root
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T11:11:49.00964+00:00
-- url     : https://prove2.me/theorems/f9d6259c-a030-440d-87dc-cdc5c8912fe2
-- title:
--   Positive Esscher root forces subcritical discounted jump-tail kernel
-- statement:
--   Let φ>0 solve δφ-J(φ)=q>0 with J(φ)=∫_(0,infinity)(1-e^(-φz))ν(dz). If the integrands are integrable, the discounted jump first moment α=∫ z e^(-φ z)ν(dz) is strictly smaller than δ. Proof uses the universal inequality t*e^(-t)≤1-e^(-t) from e^t≥1+t, integrated for positive jump magnitudes, followed by division by φ. The resulting α<δ makes the root-shifted positive geometric renewal series have finite total mass, avoiding a Tauberian theorem for the tilted scale asymptotic. This is a key deterministic bridge for the remaining Avram BV/AC theorem.
-- source:
--   Bounded-variation Lévy–Khintchine root identity; canonical Mathlib Real.add_one_le_exp and setIntegral_mono_on.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped ENNReal

theorem AvramDividend.Classical.esscher_jump_tail_mass_lt_drift_of_positive_root
    (ν : Measure ℝ) (δ φ q : ℝ)
    (hφ : 0 < φ) (hq : 0 < q)
    (hA : IntegrableOn (fun z : ℝ => z * Real.exp (-(φ * z)))
      (Ioi (0 : ℝ)) ν)
    (hJ : IntegrableOn (fun z : ℝ => 1 - Real.exp (-(φ * z)))
      (Ioi (0 : ℝ)) ν)
    (hroot : δ * φ -
      (∫ z in Ioi (0 : ℝ), 1 - Real.exp (-(φ * z)) ∂ν) = q) :
    (∫ z in Ioi (0 : ℝ), z * Real.exp (-(φ * z)) ∂ν) < δ := by sorry
