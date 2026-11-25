-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_unit_crt
-- name    : Formalism.LFunctionChainParameters.LHost.exists_unit_crt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:24:02.936821+00:00
-- url     : https://prove2.me/theorems/49ec49e1-ccde-40a4-86e1-1d6ba8956577
-- title:
--   LHost: exists unit crt
-- statement:
--   The LHost construction uses the exists unit crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L49-L62

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

theorem Formalism.LFunctionChainParameters.LHost.exists_unit_crt {N a b : ℕ} (hN : N = a * b) (hab : a.Coprime b) (ha : a ∣ N) (hb : b ∣ N)
    (x : (ZMod a)ˣ) (y : (ZMod b)ˣ) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap ha u = x ∧ ZMod.unitsMap hb u = y := by sorry
