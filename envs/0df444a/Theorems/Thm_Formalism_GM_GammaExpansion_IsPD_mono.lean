-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mono
-- name    : Formalism.GM.GammaExpansion.IsPD.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:49.973565+00:00
-- url     : https://prove2.me/theorems/2d24802d-db09-4c75-bb48-c577438edea3
-- title:
--   Is PD: mono
-- statement:
--   The Is PD construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L689-L691
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L689-L691

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open Polynomial Finset
variable {k : Type} [Field k] [CharZero k]

theorem Formalism.GM.GammaExpansion.IsPD.mono {N0 d d' : ℕ} {g : ℕ → k} (h : IsPD N0 d g) (hd : d ≤ d') : IsPD N0 d' g := by sorry
