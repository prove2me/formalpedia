-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locLen_exact
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.locLen_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:24.017249+00:00
-- url     : https://prove2.me/theorems/78bc6c53-c08b-454a-8083-c02f746ba0e8
-- title:
--   slope Lattice Data: loc Len exact
-- statement:
--   The slope Lattice Data construction uses the loc Len exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L503-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L503-L509

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {R : Type} [CommRing R]

theorem Formalism.LFunctionChainParameters.slopeLatticeData.locLen_exact (w : Ideal R) [w.IsPrime] {N M P : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    locLen w M = locLen w N + locLen w P := by sorry
