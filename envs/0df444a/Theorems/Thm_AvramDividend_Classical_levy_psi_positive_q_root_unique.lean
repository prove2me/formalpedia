-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_psi_positive_q_root_unique
-- name    : AvramDividend.Classical.levy_psi_positive_q_root_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:32:51.843988+00:00
-- url     : https://prove2.me/theorems/09d90880-cbf4-4010-a233-bfffdf7734c2
-- title:
--   Uniqueness of a positive q-root of the spectrally negative Lévy exponent
-- statement:
--   Given q>0 and two strictly positive reals phi and eta with the same Lévy exponent value ψ(phi)=ψ(eta)=q, prove phi=eta. The already proved theorem levy_psi_positive_secant_monotone states ψ(t)/t is nondecreasing for t>0. If phi<eta, that secant inequality becomes q/phi≤q/eta, impossible for q>0. Similarly eta<phi is impossible. This allows an existentially supplied Esscher root and its tilted monotonicity to be transferred to any independently supplied positive root in the main uniform-bound target.

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_psi_positive_q_root_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ η : ℝ) (hq : 0 < q)
    (hφ : 0 < φ) (hη : 0 < η)
    (hrootφ : X.ψ φ = q) (hrootη : X.ψ η = q) :
    φ = η := by sorry
