-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_localUnits_iff
-- name    : Formalism.LFunctionChainParameters.LHost.mem_localUnits_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:18.081816+00:00
-- url     : https://prove2.me/theorems/8148e332-8333-4091-bbd9-1eea1ef90816
-- title:
--   LHost: mem local Units iff
-- statement:
--   The LHost construction uses the mem local Units iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L33-L36

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

theorem Formalism.LFunctionChainParameters.LHost.mem_localUnits_iff {N : ℕ} [NeZero N] (p : ℕ) (u : (ZMod N)ˣ) :
    u ∈ localUnits N p ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] := by sorry
