-- Prove2me | Theorems.Thm_Formalism_mxS_mellin
-- name    : Formalism.mxS_mellin
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:16.919607+00:00
-- url     : https://prove2.me/theorems/68e5c660-8193-4d2e-a629-5eb22f3a60f5
-- title:
--   Formalism: mx S mellin
-- statement:
--   The Formalism construction uses the mx S mellin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L30-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L30-L90

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

theorem Formalism.mxS_mellin {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by sorry
