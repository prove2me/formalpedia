-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_zetaQuasi_of
-- name    : Formalism.L2.Th1.F.zetaQuasi_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:10.728114+00:00
-- url     : https://prove2.me/theorems/56acca03-394b-48cb-b07a-ba47b9e81fdb
-- title:
--   F: zeta Quasi of
-- statement:
--   The F construction uses the zeta Quasi of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L56-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L56-L79

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open WeierstrassZetaQuasiPeriod

theorem Formalism.L2.Th1.F.zetaQuasi_of (hd : ZetaHasDeriv) (ho : ZetaOdd) : ZetaQuasi := by sorry
