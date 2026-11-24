-- Prove2me | Theorems.Thm_CrystallinePoints_Pd_surjective_of_sup_smulD
-- name    : CrystallinePoints.Pd.surjective_of_sup_smulD
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:29:32.911524+00:00
-- url     : https://prove2.me/theorems/e1eabf1b-5166-4542-8889-f38787bb5ac9
-- title:
--   Pd: surjective of sup smul D
-- statement:
--   The Pd construction uses the surjective of sup smul D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoincareDeRhamDuality/DeRhamPerfectPairing/ResSurjD.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoincareDeRhamDuality/DeRhamPerfectPairing/ResSurjD.lean#L9-L40

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoincareDeRhamDuality_DeRhamPerfectPairing_ResSurjD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct
open CrystallinePoints CrystallinePoints.Pd

theorem CrystallinePoints.Pd.surjective_of_sup_smulD {R : Type} [CommRing R] {H M : Type*} [AddCommGroup H] [Module R H]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (γ : H →ₗ[R] M)
    (h : ∀ m : Ideal R, m.IsMaximal → LinearMap.range γ ⊔ m • (⊤ : Submodule R M) = ⊤) :
    Function.Surjective γ := by sorry
