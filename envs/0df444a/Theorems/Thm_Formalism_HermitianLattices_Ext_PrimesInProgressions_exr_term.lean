-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exr_term
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exr_term
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:29.849518+00:00
-- url     : https://prove2.me/theorems/5ea19e35-cf80-4f39-a8d5-cdf3dac60cbf
-- title:
--   Primes In Progressions: exr term
-- statement:
--   The Primes In Progressions construction uses the exr term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectA.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectA.lean#L66-L72

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exr_term (m e c w ρ y : ℂ) (hw : w ≠ 0) (hw1 : w - 1 ≠ 0) (hwρ : w - ρ ≠ 0)
    (hρ : ρ ≠ 0) (hρ1 : ρ - 1 ≠ 0) :
    -(m / (w - ρ)) * (e / w / (w - 1)) + m / (1 - ρ) * y / (w - 1) - (-m * (c / (ρ * (ρ - 1)))) / (w - ρ)
      + m / (ρ - 1) * ((e / w - c / ρ) / (w - ρ) - (e / w - y) / (w - 1)) = 0 := by sorry
