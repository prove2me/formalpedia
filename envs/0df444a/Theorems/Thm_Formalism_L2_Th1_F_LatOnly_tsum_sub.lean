-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_LatOnly_tsum_sub
-- name    : Formalism.L2.Th1.F.LatOnly.tsum_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:15.304808+00:00
-- url     : https://prove2.me/theorems/31f2f85a-1d3a-4f2d-adce-49240631e4df
-- title:
--   Lat Only: tsum sub
-- statement:
--   The Lat Only construction uses the tsum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L11-L14

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.LatOnly

theorem Formalism.L2.Th1.F.LatOnly.tsum_sub {Λ Λ' : Submodule ℤ ℂ} (h : Λ = Λ') (f : ℂ → ℂ) :
    ∑' l : Λ, f (l : ℂ) = ∑' l : Λ', f (l : ℂ) := by sorry
