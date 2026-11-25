-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhl_pole
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_pole
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:14.164991+00:00
-- url     : https://prove2.me/theorems/450de617-2c57-4675-b17a-8e295d45f987
-- title:
--   Primes In Progressions: dhl pole
-- statement:
--   The Primes In Progressions construction uses the dhl pole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHLocalA.lean#L66-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHLocalA.lean#L66-L81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalA
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_pole (k : ℕ) (s : ℂ) (hs : s ≠ 1) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z : ℂ => 1 / (z - 1)) s
      = 1 / (s - 1) ^ (k + 1) := by sorry
