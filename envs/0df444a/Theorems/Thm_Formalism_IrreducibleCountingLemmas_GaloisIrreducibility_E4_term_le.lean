-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_term_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:32.460803+00:00
-- url     : https://prove2.me/theorems/736bf457-fdb2-435f-bdc1-cff48cd4c829
-- title:
--   E4: term le
-- statement:
--   The E4 construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L41-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L41-L82

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.term_le (q δ b : ℕ) (hq : 2 ≤ q) (hδ : 2 ≤ δ)
    (h : δ * b ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    (b : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤ ((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹ := by sorry
