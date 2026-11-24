-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_det_block_norm
-- name    : Formalism.GM.MeanGammaLemmas.det_block_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:36.325466+00:00
-- url     : https://prove2.me/theorems/833cd3fe-33c0-4352-8238-5f50a9b0bc4d
-- title:
--   Mean Gamma Lemmas: det block norm
-- statement:
--   The Mean Gamma Lemmas construction uses the det block norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L153-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L153-L175

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset

theorem Formalism.GM.MeanGammaLemmas.det_block_norm {F : Type} [NormedField F] {n : ℕ} (B G : Matrix (Fin n) (Fin n) F) (e : Fin n → ℕ)
    (β : ℕ → F) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ i j, B i j = if e i = e j then β (e i) * G i j else 0)
    (hG : ∀ a, c ^ (Fintype.card {b // e b = a}) ≤ ‖(G.toSquareBlock e a).det‖) :
    ∏ b, (‖β (e b)‖ * c) ≤ ‖B.det‖ := by sorry
