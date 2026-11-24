-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EtaEis_tsum_int_telescope
-- name    : Formalism.L2.Th1.F.EtaEis.tsum_int_telescope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:51.185716+00:00
-- url     : https://prove2.me/theorems/f6d6f2f1-fee5-47ab-a2fc-d9824407a871
-- title:
--   Eta Eis: tsum int telescope
-- statement:
--   The Eta Eis construction uses the tsum int telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EtaEis.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EtaEis.lean#L11-L31

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EtaEis

theorem Formalism.L2.Th1.F.EtaEis.tsum_int_telescope (a : ℤ → ℂ) (hs : Summable fun m : ℤ => a m - a (m + 1))
    (h1 : Tendsto (fun N : ℕ => a (N : ℤ)) atTop (𝓝 0))
    (h2 : Tendsto (fun N : ℕ => a (-(N : ℤ))) atTop (𝓝 0)) :
    ∑' m : ℤ, (a m - a (m + 1)) = 0 := by sorry
