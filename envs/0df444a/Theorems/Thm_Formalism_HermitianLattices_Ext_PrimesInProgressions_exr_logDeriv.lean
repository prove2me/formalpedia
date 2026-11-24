-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exr_logDeriv
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exr_logDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:52.998796+00:00
-- url     : https://prove2.me/theorems/6f09ef4f-6d35-40ea-bd6f-5e7945fe5b79
-- title:
--   Primes In Progressions: exr log Deriv
-- statement:
--   The Primes In Progressions construction uses the exr log Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectA.lean#L31-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectA.lean#L31-L64

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exr_logDeriv (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (w : ℂ) (hwS : w ∈ S) (hwZ : w ∉ Zb) (hhw : h w ≠ 0) :
    deriv f w / f w = (∑ ρ ∈ Zb, (m ρ : ℂ) / (w - ρ)) + deriv h w / h w := by sorry
