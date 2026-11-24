-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_StdChar_ext_alg
-- name    : Formalism.L2.SG.Pf.StdChar.ext_alg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:35:50.646566+00:00
-- url     : https://prove2.me/theorems/7c79e0e9-bd75-475a-b616-c2c672e5d60d
-- title:
--   Std Char: ext alg
-- statement:
--   The Std Char construction uses the ext alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/StdChar.lean#L202-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/StdChar.lean#L202-L207

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem Formalism.L2.SG.Pf.StdChar.ext_alg (w : InfinitePlace F) (a : F) :
    InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) a) w) = w.embedding a := by sorry
