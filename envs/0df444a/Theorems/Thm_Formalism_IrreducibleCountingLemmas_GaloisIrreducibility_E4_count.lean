-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_count
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.count
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:55.531154+00:00
-- url     : https://prove2.me/theorems/d6a678af-6204-4d3c-8c51-0ebe82ab955e
-- title:
--   E4: count
-- statement:
--   The E4 construction uses the count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L222-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L222-L290

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.count (δ : ℕ) (c₀ : Kˣ) :
    δ * (Bset K δ c₀).card ≤
      ∑ l ∈ (Fintype.card K ^ δ - 1).primeFactors, l ^ padicValNat l (Fintype.card K ^ δ - 1) := by sorry
