-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_hsInner_add_smul_right
-- name    : Formalism.FourierDecayAlt.P5.hsInner_add_smul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:25.160114+00:00
-- url     : https://prove2.me/theorems/add9122c-0186-4c4c-9b56-15a1809bbac2
-- title:
--   P5: hs Inner add smul right
-- statement:
--   The P5 construction uses the hs Inner add smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsInnerAddSmulRight.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsInnerAddSmulRight.lean#L22-L25

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P5.hsInner_add_smul_right (A C C' : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner A (C + a • C') = B.hsInner A C + conj a * B.hsInner A C' := by sorry
