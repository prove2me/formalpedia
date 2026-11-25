-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_isoCount_diag
-- name    : Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:34.463323+00:00
-- url     : https://prove2.me/theorems/e5fe3bb3-64ba-43ed-ba7d-c4aba3aa0c11
-- title:
--   Isotropic Counts: iso Count diag
-- statement:
--   The Isotropic Counts construction uses the iso Count diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsoCountOneInert.lean#L121-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsoCountOneInert.lean#L121-L137

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MapMkConjTranspose
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IsotropicCounts
open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

theorem Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    (isoCount 𝔭 (k + 1) (diagonal u) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((k + 1) * m ^ 2) * alphaStd K 𝔭 m := by sorry
