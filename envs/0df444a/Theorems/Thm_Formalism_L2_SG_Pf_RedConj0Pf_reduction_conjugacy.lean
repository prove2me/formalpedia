-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_reduction_conjugacy
-- name    : Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:48.627787+00:00
-- url     : https://prove2.me/theorems/cff7ea50-f71a-4e17-b039-49ffccf9ffe8
-- title:
--   Red Conj0 Pf: reduction conjugacy
-- statement:
--   The Red Conj0 Pf construction uses the reduction conjugacy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L80-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L80-L208

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionConjugacy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin

theorem Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy : Formalism.L2.SG.Pf.RowDictPf.RedConj0 := by sorry
