-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv_super
-- name    : Formalism.FourierDecayAlt.P.C2x2.ut_inv_super
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:52.108679+00:00
-- url     : https://prove2.me/theorems/6fc2d840-c247-436b-8e40-9ccf76233e07
-- title:
--   C2x2: ut inv super
-- statement:
--   The C2x2 construction uses the ut inv super property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L79-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L79-L94

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x2.ut_inv_super {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a : Fin m) (h : a.val + 1 < m) :
    u⁻¹ a ⟨a.val + 1, h⟩ = -u a ⟨a.val + 1, h⟩ := by sorry
