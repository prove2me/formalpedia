-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_apply
-- name    : Formalism.LFunctionChainParameters.LHost.recMap_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:24:01.001489+00:00
-- url     : https://prove2.me/theorems/ad029406-1790-4bc3-8553-14c82f3901ce
-- title:
--   LHost: rec Map apply
-- statement:
--   The LHost construction uses the rec Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L402-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L402-L405

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

theorem Formalism.LFunctionChainParameters.LHost.recMap_apply (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (u : (ZMod (hostN e q d))ˣ) :
    Multiplicative.toAdd (recMap e q d u)
      = ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)),
        Additive.ofMul (hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by sorry
