-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameExtension_frame_snoc
-- name    : Formalism.FourierDecayAlt.P.FrameExtension.frame_snoc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:10:18.065986+00:00
-- url     : https://prove2.me/theorems/06ee8430-a1d0-4cbd-aab0-792dfb201175
-- title:
--   Frame Extension: frame snoc
-- statement:
--   The Frame Extension construction uses the frame snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameExtension.lean#L37-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameExtension.lean#L37-L65

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameExtension
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.FrameExtension.frame_snoc {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    IsFrameOf k r [z] (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e) := by sorry
