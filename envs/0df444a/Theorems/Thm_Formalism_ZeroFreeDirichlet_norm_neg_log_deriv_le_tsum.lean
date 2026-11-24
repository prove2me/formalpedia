-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_neg_log_deriv_le_tsum
-- name    : Formalism.ZeroFreeDirichlet.norm_neg_log_deriv_le_tsum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:59.771358+00:00
-- url     : https://prove2.me/theorems/07188777-cfeb-4ac9-9ff0-e675d47d510b
-- title:
--   Zero Free Dirichlet: norm neg log deriv le tsum
-- statement:
--   The Zero Free Dirichlet construction uses the norm neg log deriv le tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L106-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L106-L126

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.ZeroFreeDirichlet.norm_neg_log_deriv_le_tsum {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖negLD χ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by sorry
