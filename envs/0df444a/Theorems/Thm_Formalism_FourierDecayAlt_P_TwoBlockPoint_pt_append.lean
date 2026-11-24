-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append
-- name    : Formalism.FourierDecayAlt.P.TwoBlockPoint.pt_append
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:04.566661+00:00
-- url     : https://prove2.me/theorems/3c78f1be-1041-45a6-a707-0b29b999fef0
-- title:
--   Two Block Point: pt append
-- statement:
--   The Two Block Point construction uses the pt append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L493-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L493-L516

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
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.TwoBlockPoint.pt_append (l l' : List ℕ) (T T₁ T₂ : ℕ → Kˣ) (h₁ : ∀ b, b < l.length → T b = T₁ b)
    (h₂ : ∀ b, b < l'.length → T (l.length + b) = T₂ b) (hN : (l ++ l').sum = l.sum + l'.sum) :
    pt (l ++ l') T = blkM hN (pt l T₁) 0 0 (pt l' T₂) := by sorry
