-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cast_eq_one_iff
-- name    : Formalism.LFunctionChainParameters.LHost.cast_eq_one_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:24:41.052029+00:00
-- url     : https://prove2.me/theorems/12d9b9ca-bf7b-44f7-bc74-a107288cbbb6
-- title:
--   LHost: cast eq one iff
-- statement:
--   The LHost construction uses the cast eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L21-L23

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

theorem Formalism.LFunctionChainParameters.LHost.cast_eq_one_iff {N : ℕ} [NeZero N] (x : ZMod N) (c : ℕ) :
    (x.cast : ZMod c) = 1 ↔ x.val ≡ 1 [MOD c] := by sorry
