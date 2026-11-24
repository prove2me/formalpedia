-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_key
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:04.129624+00:00
-- url     : https://prove2.me/theorems/bb17f194-a420-4129-aa75-c3c3c8669efc
-- title:
--   E4: key
-- statement:
--   The E4 construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L138-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L138-L212

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.key (P : K[X]) (hP : Irreducible P) (hm : P.Monic) (x : L) (hx : aeval x P = 0)
    (hx0 : x ≠ 0) (c₀ : Kˣ) (l : ℕ) (hl : l.Prime)
    (h : primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))) (hq : 3 ≤ Fintype.card K) :
    ∃ l' ∈ (Fintype.card K ^ P.natDegree - 1).primeFactors,
      P ∣ X ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1)) -
        C ((c₀ : K) ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1))) := by sorry
