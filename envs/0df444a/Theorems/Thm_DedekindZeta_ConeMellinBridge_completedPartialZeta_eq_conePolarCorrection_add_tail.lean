-- Prove2me | Theorems.Thm_DedekindZeta_ConeMellinBridge_completedPartialZeta_eq_conePolarCorrection_add_tail
-- name    : DedekindZeta.ConeMellinBridge.completedPartialZeta_eq_conePolarCorrection_add_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:40:18.392845+00:00
-- url     : https://prove2.me/theorems/b43970d6-e698-40b5-83c3-7702aa29444c
-- title:
--   Cone Mellin Bridge: completed Partial Zeta eq cone Polar Correction add tail
-- statement:
--   **The completed partial zeta, polar part + regularised tail.** On `Re s > 1`,
--   `completedPartialZeta K 𝔞 s` equals its prefactor times
--   `conePolarCorrection K 𝔞 s + mellinTail …`. This is the assembly-facing
--   spelling of the final-assembly step 3: the `+1`/`−1` correction `𝒞(𝔞,s)`
--   appears as the explicit summand `conePolarCorrection K 𝔞 s` (the genuine polar
--   head carrying the simple poles of `ζ_K` at `s = 0, 1` — see
--   `conePolarCorrection_residue_zero`/`_one`), and is therefore *removed from the
--   assembly by being replaced with its true value*, **not** dropped as `0`. The
--   remaining `mellinTail` summand is the entire regularised dual contribution.
--
--   Immediate from `completedPartialZeta_eq_mellinContinuation` together with
--   `mellinContinuation_eq_conePolarCorrection_add_tail`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L236-L245
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L236-L245

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
variable {K}

theorem DedekindZeta.ConeMellinBridge.completedPartialZeta_eq_conePolarCorrection_add_tail (𝔞 : Ideal (𝓞 K))
    (hne : 𝔞 ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    DedekindZeta.completedPartialZeta K 𝔞 s
      = (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s
          * (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))
          * (conePolarCorrection K 𝔞 s
              + mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
                  (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s) := by sorry
