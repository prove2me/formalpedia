-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_of_modEq
-- name    : Formalism.LFunctionChainParameters.LHost.recMap_of_modEq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:56.809016+00:00
-- url     : https://prove2.me/theorems/3fa9f16f-3d15-4a9c-b3f7-d8048672925c
-- title:
--   LHost: rec Map of mod Eq
-- statement:
--   The LHost construction uses the rec Map of mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L335-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L335-L346

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

theorem Formalism.LFunctionChainParameters.LHost.recMap_of_modEq {e q d : ℕ} [Fact q.Prime] [Fact d.Prime] [NeZero (hostN e q d)] (u : (ZMod (hostN e q d))ˣ)
    (kd kq k2 : ℕ) (hk2 : k2.Coprime (2 ^ (e + 2)))
    (h1 : (u : ZMod (hostN e q d)).val ≡ kd [MOD d]) (h2 : (u : ZMod (hostN e q d)).val ≡ kq [MOD q])
    (h3 : (u : ZMod (hostN e q d)).val ≡ k2 [MOD 2 ^ (e + 2)]) :
    Multiplicative.toAdd (recMap e q d u)
      = ((if jacobiSym (kd : ℤ) d = 1 then 0 else 1, if jacobiSym (kq : ℤ) q = 1 then 0 else 1),
        Additive.ofMul (hcl e (ZMod.unitOfCoprime k2 hk2))) := by sorry
