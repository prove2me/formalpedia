-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_AAvop_eq
-- name    : Formalism.FourierDecayAlt.P.PBG.AAvop_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:20:16.69923+00:00
-- url     : https://prove2.me/theorems/29a7a796-7747-42ea-8ec2-e515c0ada5d3
-- title:
--   PBG: AAvop eq
-- statement:
--   The PBG construction uses the AAvop eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L259-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L259-L269

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)

theorem Formalism.FourierDecayAlt.P.PBG.AAvop_eq (m : ℕ) (hm : m ≤ r) (ell : ℂ) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    C3.AAvop k r m hm ell f.1 g₀ = ((C3.AAv k r (fun a b => EHt (E := E) U₀ hU₀ a b) (y0 g₀) m hm ell) f).1 g₀ := by sorry
