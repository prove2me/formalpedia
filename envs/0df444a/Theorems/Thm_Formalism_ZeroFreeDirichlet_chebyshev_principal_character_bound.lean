-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_principal_character_bound
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_principal_character_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:45.267277+00:00
-- url     : https://prove2.me/theorems/85edbe5b-37de-4c6e-a2b1-f7dc5958d285
-- title:
--   Zero Free Dirichlet: chebyshev principal character bound
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev principal character bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PsiChiBoundOf.lean#L144-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PsiChiBoundOf.lean#L144-L237

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

theorem Formalism.ZeroFreeDirichlet.chebyshev_principal_character_bound {q : ℕ} [NeZero q] {cg Kg c₀ y : ℝ} (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hcg : c₀ ≤ cg) (hKg : 0 ≤ Kg) (hy : 2 ≤ y)
    (hq : (q : ℝ) ≤ Real.exp (c₀ / 4 * Real.sqrt (Real.log y)))
    (hG : ∀ z : ℝ, y ≤ z → |Formalism.Gz z| ≤ Kg * z * Real.exp (-cg * Real.sqrt (Real.log z))) :
    ‖psiChi (1 : DirichletCharacter ℂ q) y - y‖ ≤
      (128 / c₀ ^ 2 + 2 + 4 * Kg) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y))
        + 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by sorry
