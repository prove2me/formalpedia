-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_congr
-- name    : Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:36.972775+00:00
-- url     : https://prove2.me/theorems/addf204e-f319-47f6-a4f9-83429d62864c
-- title:
--   Finite Classes Positive Sums: psd congr
-- statement:
--   The Finite Classes Positive Sums construction uses the psd congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L14-L19

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

theorem Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_congr {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k)
    (e : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) : IsPSD F k' := by sorry
