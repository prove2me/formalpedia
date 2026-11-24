-- Prove2me | Theorems.Thm_Formalism_mxS_mellin_real
-- name    : Formalism.mxS_mellin_real
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:19.926776+00:00
-- url     : https://prove2.me/theorems/021e8ce0-7fb8-455d-bdf6-9fd444207863
-- title:
--   Formalism: mx S mellin real
-- statement:
--   The Formalism construction uses the mx S mellin real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L92-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L92-L136

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism

theorem Formalism.mxS_mellin_real {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => mxS n x * x ^ (-σ - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), mxS n x * x ^ (-σ - 1) = (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by sorry
