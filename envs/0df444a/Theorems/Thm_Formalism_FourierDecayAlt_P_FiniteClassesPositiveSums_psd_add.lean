-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_add
-- name    : Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:15.62619+00:00
-- url     : https://prove2.me/theorems/63e27df9-fde7-42a8-adf2-0aa541e8a82e
-- title:
--   Finite Classes Positive Sums: psd add
-- statement:
--   The Finite Classes Positive Sums construction uses the psd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L24-L31

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_add {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k) (h' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by sorry
