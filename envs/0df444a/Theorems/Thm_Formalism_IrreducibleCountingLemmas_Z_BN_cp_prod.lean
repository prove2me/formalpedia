-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_prod
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.cp_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:47.430185+00:00
-- url     : https://prove2.me/theorems/1bef7e58-3084-4430-96c4-0bc228f1a161
-- title:
--   BN: cp prod
-- statement:
--   The BN construction uses the cp prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbittAlg.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbittAlg.lean#L26-L30

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W S : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup S] [Module A S]

theorem Formalism.IrreducibleCountingLemmas.Z.BN.cp_prod [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    cp k (V × W) a = cp k V a * cp k W a := by sorry
