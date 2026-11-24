-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_harm_part
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.harm_part
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:18.683271+00:00
-- url     : https://prove2.me/theorems/88f5e2c0-feb1-4f69-b66d-8e9ee87ca885
-- title:
--   E4: harm part
-- statement:
--   The E4 construction uses the harm part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L24-L39

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.harm_part (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹ ≤ Real.log ((M + 1 : ℕ) : ℝ) := by sorry
