-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_sqWeight_irred
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.sqWeight_irred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:55.682804+00:00
-- url     : https://prove2.me/theorems/15fd28e6-ae2b-4a31-a811-c4f1d2db42ea
-- title:
--   E4: sq Weight irred
-- statement:
--   The E4 construction uses the sq Weight irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L292-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L292-L297

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.sqWeight_irred (P : K[X]) (hP : Irreducible P) (hm : P.Monic) :
    sqWeight P = ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by sorry
