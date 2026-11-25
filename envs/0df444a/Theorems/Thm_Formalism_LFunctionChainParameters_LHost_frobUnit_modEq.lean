-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobUnit_modEq
-- name    : Formalism.LFunctionChainParameters.LHost.frobUnit_modEq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:46.262319+00:00
-- url     : https://prove2.me/theorems/163302b7-e760-4f12-a576-96a91ff80d8f
-- title:
--   LHost: frob Unit mod Eq
-- statement:
--   The LHost construction uses the frob Unit mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L86-L89

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

theorem Formalism.LFunctionChainParameters.LHost.frobUnit_modEq {N p : ℕ} [NeZero N] (hp : p.Prime) :
    ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ p [MOD ordCompl[p] N] ∧
      ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD ordProj[p] N] := by sorry
