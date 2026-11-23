-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_span_baseChange
-- name    : Formalism.LFunctionChainParameters.LLcv.span_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:38.940161+00:00
-- url     : https://prove2.me/theorems/88bf4dd5-6636-4969-a685-c9d48a3d1c96
-- title:
--   LLcv: span base Change
-- statement:
--   The LLcv construction uses the span base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L642-L664
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L642-L664

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.LFunctionChainParameters.LLcv.span_baseChange {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K)
    (hg : IsUnit g.det) :
    Submodule.span K (Set.range fun a => ∑ c, g c a • e c) = Submodule.span K (Set.range e) := by sorry
