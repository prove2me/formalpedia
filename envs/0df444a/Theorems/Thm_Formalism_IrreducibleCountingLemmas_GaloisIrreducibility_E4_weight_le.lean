-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_weight_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.weight_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:59.508331+00:00
-- url     : https://prove2.me/theorems/93551c0b-d6f3-42a6-9865-5349c25795c9
-- title:
--   E4: weight le
-- statement:
--   The E4 construction uses the weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L299-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L299-L350

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.weight_le (N : ℕ) (c₀ : Kˣ) (hq : 3 ≤ Fintype.card K) :
    wtOf (fun c : Fin N → K => sqWeight (monicOf c)) {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
        l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} ≤
      ∑ δ ∈ Finset.Icc 1 N, ((Bset K δ c₀).card : ℝ) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by sorry
