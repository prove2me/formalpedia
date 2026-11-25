-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhl_triv
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_triv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:44:18.828589+00:00
-- url     : https://prove2.me/theorems/0d8f2fa2-da39-4761-a04b-1cb9373421d4
-- title:
--   Primes In Progressions: dhl triv
-- statement:
--   The Primes In Progressions construction uses the dhl triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHLocal.lean#L77-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHLocal.lean#L77-L165

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocal
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_triv (hCau : DHCauchy) (K : ℝ) (hK : 10400 ≤ K) (M : ℕ) [NeZero M]
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M (1 : DirichletCharacter ℂ M) t := by sorry
