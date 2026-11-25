-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cF_eq
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:17.559991+00:00
-- url     : https://prove2.me/theorems/4c0c0bd1-e469-5ee4-bfb7-a92772bdfbda
-- title:
--   Hyp: c F eq
-- statement:
--   The Hyp construction uses the c F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperA.lean#L21-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperA.lean#L21-L63

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_eq (N : ℕ) :
    cF χ N = ∑ b ∈ Ioc 0 N, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) := by sorry
