-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_prod_one_sub_inv_mul_X
-- name    : Formalism.IrreducibleCountingLemmas.TW.prod_one_sub_inv_mul_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:26.739893+00:00
-- url     : https://prove2.me/theorems/f38d8773-2c09-41d1-8d02-867f0970c1d3
-- title:
--   TW: prod one sub inv mul X
-- statement:
--   The TW construction uses the prod one sub inv mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWHeckeDetFactors.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWHeckeDetFactors.lean#L7-L20

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWHeckeDetFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW

theorem Formalism.IrreducibleCountingLemmas.TW.prod_one_sub_inv_mul_X {k : Type} [Field k] (s : Multiset k) (hs : ∀ a ∈ s, a ≠ 0) :
    (s.map (fun a => (1 : k[X]) - C a⁻¹ * X)).prod * C (s.map (fun a => 0 - a)).prod =
      (s.map (fun a => (X : k[X]) - C a)).prod := by sorry
