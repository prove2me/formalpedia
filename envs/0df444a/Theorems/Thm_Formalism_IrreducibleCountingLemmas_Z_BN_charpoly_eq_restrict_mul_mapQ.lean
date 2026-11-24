-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_charpoly_eq_restrict_mul_mapQ
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_eq_restrict_mul_mapQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:40.810558+00:00
-- url     : https://prove2.me/theorems/26b0dc25-159f-4778-ac50-5cc0a4534872
-- title:
--   BN: charpoly eq restrict mul map Q
-- statement:
--   The BN construction uses the charpoly eq restrict mul map Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L13-L46

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
open Module.Basis

theorem Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_eq_restrict_mul_mapQ {R V : Type*} [Field R] [AddCommGroup V]
    [Module R V] [Module.Finite R V] (W : Submodule R V) (e : V →ₗ[R] V) (he : W ≤ W.comap e) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by sorry
