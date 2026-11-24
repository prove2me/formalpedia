-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_log_deriv_eq_lseries_re_im
-- name    : Formalism.ZeroFreeDirichlet.neg_log_deriv_eq_lseries_re_im
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:23.63803+00:00
-- url     : https://prove2.me/theorems/ab53f070-f8b6-44be-a585-c006c791ec3e
-- title:
--   Zero Free Dirichlet: neg log deriv eq lseries re im
-- statement:
--   The Zero Free Dirichlet construction uses the neg log deriv eq lseries re im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L93-L104

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

theorem Formalism.ZeroFreeDirichlet.neg_log_deriv_eq_lseries_re_im {w : ℂ} (hw : 1 < w.re) :
    negLD χ w = LSeries (fun n => (vonMangoldtCharRe χ n : ℂ)) w +
      I * LSeries (fun n => (vonMangoldtCharIm χ n : ℂ)) w := by sorry
