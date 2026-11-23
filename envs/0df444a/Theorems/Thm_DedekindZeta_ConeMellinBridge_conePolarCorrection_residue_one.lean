-- Prove2me | Theorems.Thm_DedekindZeta_ConeMellinBridge_conePolarCorrection_residue_one
-- name    : DedekindZeta.ConeMellinBridge.conePolarCorrection_residue_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:50:34.048659+00:00
-- url     : https://prove2.me/theorems/6333888f-6441-42ac-9808-1709cf199e78
-- title:
--   Cone Mellin Bridge: cone Polar Correction residue one
-- statement:
--   **The correction `𝒞` has a simple pole at `s = 1` with residue `C·b₀ = C·V`.**
--   `lim_{s→1} (s−1)·𝒞(𝔞,s) = (covolume K 𝔞)⁻¹ · surfaceVolume K`. The residue
--   powering the simple pole of `ζ_K` at `s = 1`. Proved from the closed form.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L189-L211
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L189-L211

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

theorem DedekindZeta.ConeMellinBridge.conePolarCorrection_residue_one (𝔞 : Ideal (𝓞 K)) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * conePolarCorrection K 𝔞 s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K)) := by sorry
