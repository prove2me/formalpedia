-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitsMap_eq_unitOfCoprime_iff
-- name    : Formalism.LFunctionChainParameters.LHost.unitsMap_eq_unitOfCoprime_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:39:43.71217+00:00
-- url     : https://prove2.me/theorems/f2a81a65-9a51-5156-8630-800a8ee3229e
-- title:
--   LHost: units Map eq unit Of Coprime iff
-- statement:
--   The LHost construction uses the units Map eq unit Of Coprime iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L29-L31

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

theorem Formalism.LFunctionChainParameters.LHost.unitsMap_eq_unitOfCoprime_iff {N c k : ℕ} [NeZero N] (h : c ∣ N) (hk : k.Coprime c) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = ZMod.unitOfCoprime k hk ↔ (u : ZMod N).val ≡ k [MOD c] := by sorry
