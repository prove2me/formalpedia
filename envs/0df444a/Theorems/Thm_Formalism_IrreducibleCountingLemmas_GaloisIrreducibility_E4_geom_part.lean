-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_geom_part
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.geom_part
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:28.87438+00:00
-- url     : https://prove2.me/theorems/d82d9864-1e4e-4245-b443-7026edc84b36
-- title:
--   E4: geom part
-- statement:
--   The E4 construction uses the geom part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L10-L22

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.geom_part (Q : ℝ) (hQ : 1 < Q) (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ ≤ (1 - (Q ^ M)⁻¹) / (Q - 1) := by sorry
