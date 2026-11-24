-- Prove2me | Theorems.Thm_Formalism_GM_TM_grid_average
-- name    : Formalism.GM.TM.grid_average
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:37.859053+00:00
-- url     : https://prove2.me/theorems/70a73a74-6dc8-4fab-b479-a26ff3ae9cf6
-- title:
--   TM: grid average
-- statement:
--   The TM construction uses the grid average property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L256-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L256-L278

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open Finset

theorem Formalism.GM.TM.grid_average {t : ℕ} (s : Fin t → Finset ℕ) (bad : (Fin t → ℕ) → ℝ) (B Dm : Fin t → (Fin t → ℕ) → ℝ)
    (eps : Fin t → ℝ) (hcard : ∀ i, 0 < (s i).card)
    (h1 : ∀ n ∈ Fintype.piFinset s, bad n ≤ ∑ i, B i n)
    (h2 : ∀ i, ∀ n ∈ Fintype.piFinset s, ∑ y ∈ s i, B i (Function.update n i y) ≤ (s i).card * (eps i * Dm i n)) :
    (∑ n ∈ Fintype.piFinset s, bad n) / (Fintype.piFinset s).card ≤
      ∑ i, eps i * ((∑ n ∈ Fintype.piFinset s, Dm i n) / (Fintype.piFinset s).card) := by sorry
