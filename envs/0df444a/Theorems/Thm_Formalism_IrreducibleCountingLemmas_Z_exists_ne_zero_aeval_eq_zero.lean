-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_exists_ne_zero_aeval_eq_zero
-- name    : Formalism.IrreducibleCountingLemmas.Z.exists_ne_zero_aeval_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:59.223199+00:00
-- url     : https://prove2.me/theorems/0d201908-adae-40ad-aad5-fb3c1fa282fe
-- title:
--   Z: exists ne zero aeval eq zero
-- statement:
--   The Z construction uses the exists ne zero aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ExistsNeZeroAevalEqZero.lean#L8-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ExistsNeZeroAevalEqZero.lean#L8-L41

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_SchurOrthogonalityCompact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped TensorProduct
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z

theorem Formalism.IrreducibleCountingLemmas.Z.exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by sorry
