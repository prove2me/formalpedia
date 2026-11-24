-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_arith
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:15.272266+00:00
-- url     : https://prove2.me/theorems/7a545cdd-0441-4b39-b03b-8cdff1c6b5da
-- title:
--   E4: arith
-- statement:
--   The E4 construction uses the arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L84-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L84-L114

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.arith (q N : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (b : ℕ → ℕ) (m : ℝ)
    (h1 : (b 1 : ℝ) * ((q : ℝ) - 1)⁻¹ ≤ m)
    (h2 : ∀ δ, 2 ≤ δ → δ * b δ ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    ∑ δ ∈ Finset.Icc 1 N, (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      m + (1 + Real.log N) / ((q : ℝ) - 1) := by sorry
