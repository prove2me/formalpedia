-- Prove2me | Theorems.Thm_Formalism_integrable_tsum_of_nonneg
-- name    : Formalism.integrable_tsum_of_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:34.524471+00:00
-- url     : https://prove2.me/theorems/5b879690-45dc-4382-a957-0cc39596590f
-- title:
--   Formalism: integrable tsum of nonneg
-- statement:
--   The Formalism construction uses the integrable tsum of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L138-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L138-L154

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

theorem Formalism.integrable_tsum_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : ℕ → α → ℝ} (hφ : ∀ n, Integrable (φ n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ φ n x)
    (hsx : ∀ x, Summable (fun n => φ n x)) (hs : Summable fun n => ∫ x, φ n x ∂μ) :
    Integrable (fun x => ∑' n, φ n x) μ := by sorry
