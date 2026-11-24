-- Prove2me | Theorems.Thm_Formalism_UG_P_csCovol_det_le
-- name    : Formalism.UG.P.csCovol_det_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:24.86357+00:00
-- url     : https://prove2.me/theorems/25ca0737-1ab7-4e5b-a73c-2aa484cd2cef
-- title:
--   P: cs Covol det le
-- statement:
--   The P construction uses the cs Covol det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L27-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L27-L47

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.csCovol_det_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ) (hG : 0 < G.det) (D : ℤ) (hD0 : D ≠ 0)
    (P : Matrix (Fin N) (Fin N) ℤ) (hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1) :
    G.det ≤ (|D| : ℚ) ^ N := by sorry
