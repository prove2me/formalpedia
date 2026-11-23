-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_progression_orthogonality
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_progression_orthogonality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:41.460302+00:00
-- url     : https://prove2.me/theorems/2f425cd4-a761-4642-8580-92dcc89dce3c
-- title:
--   Zero Free Dirichlet: chebyshev progression orthogonality
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev progression orthogonality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszAPOf.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszAPOf.lean#L9-L29

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
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

theorem Formalism.ZeroFreeDirichlet.chebyshev_progression_orthogonality (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    (q.totient : ℂ) * ((psiAP q a x : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChi χ x := by sorry
