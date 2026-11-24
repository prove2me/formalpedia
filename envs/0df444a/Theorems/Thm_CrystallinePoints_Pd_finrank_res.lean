-- Prove2me | Theorems.Thm_CrystallinePoints_Pd_finrank_res
-- name    : CrystallinePoints.Pd.finrank_res
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:39.521026+00:00
-- url     : https://prove2.me/theorems/5e545b94-4f24-49f8-a1a3-8ad0e6eb7939
-- title:
--   Pd: finrank res
-- statement:
--   The Pd construction uses the finrank res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoincareDeRhamDuality/DeRhamPerfectPairing/ResSurjD.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoincareDeRhamDuality/DeRhamPerfectPairing/ResSurjD.lean#L42-L51

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

theorem CrystallinePoints.Pd.finrank_res {R : Type} [CommRing R] (m : Ideal R) [hm : m.IsMaximal] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.rankAtStalk M (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by sorry
