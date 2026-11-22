-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_asAlgebraHom_apply_eq_sum
-- name    : Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:35.717154+00:00
-- url     : https://prove2.me/theorems/cdd4b842-4b8e-4b72-bfa9-33250afb9dd6
-- title:
--   TW: as Algebra Hom apply eq sum
-- statement:
--   The TW construction uses the as Algebra Hom apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWCutOperator.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWCutOperator.lean#L6-L11

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWCentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWCutOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW

theorem Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : MonoidAlgebra K G) (v : V) :
    ρ.asAlgebraHom x v = ∑ g ∈ x.coeff.support, x.coeff g • ρ g v := by sorry
