-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_legU_of_modEq
-- name    : Formalism.LFunctionChainParameters.LHost.legU_of_modEq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:52:43.731948+00:00
-- url     : https://prove2.me/theorems/14863322-5a26-481a-8d9b-e02edf0b59f7
-- title:
--   LHost: leg U of mod Eq
-- statement:
--   The LHost construction uses the leg U of mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L329-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L329-L333

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
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)

theorem Formalism.LFunctionChainParameters.LHost.legU_of_modEq {N l : ℕ} [NeZero N] [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) (k : ℕ)
    (hk : (u : ZMod N).val ≡ k [MOD l]) : ((legU N l h u : ℤˣ) : ℤ) = jacobiSym (k : ℤ) l := by sorry
