-- Prove2me | Theorems.Thm_Formalism_rint_Gchi
-- name    : Formalism.rint_Gchi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:10.668071+00:00
-- url     : https://prove2.me/theorems/6141e583-e0eb-4ee7-ad24-d41659f216ad
-- title:
--   Formalism: rint Gchi
-- statement:
--   The Formalism construction uses the rint Gchi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L54-L68

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
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
open ArithmeticFunction

theorem Formalism.rint_Gchi (h3 : MellinSgen) (h5 : MellinElem) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) (Ioi 1) := by sorry
