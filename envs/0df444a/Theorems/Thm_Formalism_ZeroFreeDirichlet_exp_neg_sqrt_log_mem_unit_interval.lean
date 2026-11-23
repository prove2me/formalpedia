-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_neg_sqrt_log_mem_unit_interval
-- name    : Formalism.ZeroFreeDirichlet.exp_neg_sqrt_log_mem_unit_interval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:53.550872+00:00
-- url     : https://prove2.me/theorems/9abef564-cf41-48ff-a888-35b7fc017670
-- title:
--   Zero Free Dirichlet: exp neg sqrt log mem unit interval
-- statement:
--   The Zero Free Dirichlet construction uses the exp neg sqrt log mem unit interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PsiChiBoundOf.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PsiChiBoundOf.lean#L31-L36

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PsiChiBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.exp_neg_sqrt_log_mem_unit_interval {c₀ y : ℝ} (hc0 : 0 < c₀) :
    0 < Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ∧
      Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ≤ 1 := by sorry
