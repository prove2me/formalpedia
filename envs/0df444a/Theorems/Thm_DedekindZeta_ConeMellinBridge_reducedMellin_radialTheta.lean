-- Prove2me | Theorems.Thm_DedekindZeta_ConeMellinBridge_reducedMellin_radialTheta
-- name    : DedekindZeta.ConeMellinBridge.reducedMellin_radialTheta
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:50:30.754499+00:00
-- url     : https://prove2.me/theorems/215cb427-e625-4233-9e71-bad222278798
-- title:
--   Cone Mellin Bridge: reduced Mellin radial Theta
-- statement:
--   `reducedMellin (radialTheta K 𝔞) (surfaceVolume K) s = mellin (orbitTheta K 𝔞) s`.
--
--   The completed radial theta `radialTheta K 𝔞 = orbitTheta K 𝔞 + surfaceVolume K`
--   restores the constant term `V = surfaceVolume K`; subtracting it back inside the
--   reduced Mellin recovers exactly the raw `mellin (orbitTheta K 𝔞)`. So the
--   regularisation `+V` changes nothing the raw cone Mellin sees — it only restores
--   the constant term that powers the polar part.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L115-L118
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L115-L118

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

theorem DedekindZeta.ConeMellinBridge.reducedMellin_radialTheta (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    reducedMellin (radialTheta K 𝔞) (surfaceVolume K) s = mellin (orbitTheta K 𝔞) s := by sorry
