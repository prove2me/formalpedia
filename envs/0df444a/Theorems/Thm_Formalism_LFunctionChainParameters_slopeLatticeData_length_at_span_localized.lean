-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_length_at_span_localized
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.length_at_span_localized
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:32.211016+00:00
-- url     : https://prove2.me/theorems/e5fabe63-5413-468a-901d-f4b8d1314ee4
-- title:
--   slope Lattice Data: length at span localized
-- statement:
--   The slope Lattice Data construction uses the length at span localized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L714-L748
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L714-L748

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.length_at_span_localized {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (w : Ideal R)
    [w.IsPrime] [Module (Localization.AtPrime w) V] [IsScalarTower R (Localization.AtPrime w) V]
    (A B : Submodule R V) (hBA : B ≤ A) (A'' : Submodule (Localization.AtPrime w) V)
    (hA : haveI := isLocalizedModule_id w.primeCompl V (Localization.AtPrime w)
      A.localized' (Localization.AtPrime w) w.primeCompl LinearMap.id = A'') :
    locLen w (A ⧸ B.comap A.subtype) = Module.length (Localization.AtPrime w)
      (A'' ⧸ (Submodule.span (Localization.AtPrime w) (B : Set V)).comap A''.subtype) := by sorry
