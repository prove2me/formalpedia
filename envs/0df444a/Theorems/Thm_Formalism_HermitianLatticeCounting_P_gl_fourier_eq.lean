-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gl_fourier_eq
-- name    : Formalism.HermitianLatticeCounting.P.gl_fourier_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:51.442798+00:00
-- url     : https://prove2.me/theorems/15b2a660-62f0-4792-abc9-1ca7c245eabd
-- title:
--   P: gl fourier eq
-- statement:
--   The P construction uses the gl fourier eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L16-L32

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

theorem Formalism.HermitianLatticeCounting.P.gl_fourier_eq (φ : ℂ → ℂ) (w : ℂ) :
    𝓕 φ w = ∫ c : ℂ, Complex.exp (2 * Complex.I *
      (((-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w)) * c).im : ℂ)) * φ c := by sorry
