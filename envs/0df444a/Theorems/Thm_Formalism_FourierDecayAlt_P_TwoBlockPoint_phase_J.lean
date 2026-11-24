-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_phase_J
-- name    : Formalism.FourierDecayAlt.P.TwoBlockPoint.phase_J
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:12.098533+00:00
-- url     : https://prove2.me/theorems/f4bc2649-dcc0-4fc0-b980-3601c44c1eb5
-- title:
--   Two Block Point: phase J
-- statement:
--   The Two Block Point construction uses the phase J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L1436-L1449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean#L1436-L1449

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
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))

theorem Formalism.FourierDecayAlt.P.TwoBlockPoint.phase_J (ψ : AddChar K ℂ) (v : lowW K h.1 h.2 × lowW K g.1 g.2)
    (u : upUniG K h.1.sum × upUniG K g.1.sum)
    (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) (Y : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    phase ψ ((lowJ hN hW v X, upJ hN u Y) : lowW K w.1 w.2 × upUniG K w.1.sum) =
      phase ψ ((v.1, u.1) : lowW K h.1 h.2 × upUniG K h.1.sum) * ψ (cornL X + cornU Y) *
        phase ψ ((v.2, u.2) : lowW K g.1 g.2 × upUniG K g.1.sum) := by sorry
