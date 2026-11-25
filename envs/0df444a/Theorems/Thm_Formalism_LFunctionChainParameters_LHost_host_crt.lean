-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_crt
-- name    : Formalism.LFunctionChainParameters.LHost.host_crt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:23:38.660843+00:00
-- url     : https://prove2.me/theorems/6a235086-d1cd-455b-93a3-97517a6b2441
-- title:
--   LHost: host crt
-- statement:
--   The LHost construction uses the host crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L407-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L407-L422

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

theorem Formalism.LFunctionChainParameters.LHost.host_crt (e : ℕ) {q d : ℕ} (h : HostHyp q d) (x2 : (ZMod (2 ^ (e + 2)))ˣ) (xq : (ZMod q)ˣ) (xd : (ZMod d)ˣ) :
    ∃ u : (ZMod (hostN e q d))ˣ, ZMod.unitsMap (two_dvd_hostN e q d) u = x2 ∧
      ZMod.unitsMap (q_dvd_hostN e q d) u = xq ∧ ZMod.unitsMap (d_dvd_hostN e q d) u = xd := by sorry
