-- Prove2me | Theorems.Thm_BornVolume_injOn_PsiN
-- name    : BornVolume.injOn_PsiN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:16.014499+00:00
-- url     : https://prove2.me/theorems/3b56398d-9735-4f2c-94c0-a17fbaf26146
-- title:
--   Born Volume: inj On Psi N
-- statement:
--   **`Ψ_N` is injective on the domain.** From `Ψ_N y = Ψ_N y'`, summing
--   recovers `S = S'` (`PsiN_sum`); then each `castSucc` coordinate cancels `S > 0`,
--   and the last coordinate is `S`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L321-L335
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L321-L335

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.injOn_PsiN : InjOn (PsiN (M := M)) domainN := by sorry
