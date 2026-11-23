-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cls_bij
-- name    : Formalism.FourierDecayAlt.P.TwoBlockPoint.cls_bij
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:45.766464+00:00
-- url     : https://prove2.me/theorems/9be12b10-88b0-4228-9d9d-b97270d22fba
-- title:
--   Two Block Point: cls bij
-- statement:
--   The Two Block Point construction uses the cls bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L993-L1002
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L993-L1002

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.TwoBlockPoint.cls_bij {ι κ : Type} (L L' : Matrix ι κ K → Matrix ι κ K)
    (hadd : ∀ U V, L (U + V) = L U + L V) (hadd' : ∀ U V, L' (U + V) = L' U + L' V)
    (hint : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L V i j ∈ R)
    (hint' : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L' V i j ∈ R)
    (hinv : ∀ U, L' (L U) = U) (hinv' : ∀ U, L (L' U) = U) :
    Function.Bijective (fun x : Matrix ι κ (KR R) => clsM R (L (outM R x))) := by sorry
