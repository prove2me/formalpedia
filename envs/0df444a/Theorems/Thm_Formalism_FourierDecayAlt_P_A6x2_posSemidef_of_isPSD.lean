-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_posSemidef_of_isPSD
-- name    : Formalism.FourierDecayAlt.P.A6x2.posSemidef_of_isPSD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:30.324775+00:00
-- url     : https://prove2.me/theorems/b7782903-1f8e-4c6c-b32d-2aa0a3e11657
-- title:
--   A6x2: pos Semidef of is PSD
-- statement:
--   The A6x2 construction uses the pos Semidef of is PSD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PosSemidefEntryBound.lean#L89-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PosSemidefEntryBound.lean#L89-L107

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x2

theorem Formalism.FourierDecayAlt.P.A6x2.posSemidef_of_isPSD {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    (Matrix.of fun x y : F => conj (k x y)).PosSemidef := by sorry
