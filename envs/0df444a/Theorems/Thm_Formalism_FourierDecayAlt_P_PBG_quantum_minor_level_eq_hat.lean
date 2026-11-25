-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_quantum_minor_level_eq_hat
-- name    : Formalism.FourierDecayAlt.P.PBG.quantum_minor_level_eq_hat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:00.51274+00:00
-- url     : https://prove2.me/theorems/516fb2ab-d363-4d4a-9f1d-184ed00c5991
-- title:
--   PBG: quantum minor level eq hat
-- statement:
--   The PBG construction uses the quantum minor level eq hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L85-L90

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
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
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem Formalism.FourierDecayAlt.P.PBG.quantum_minor_level_eq_hat (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (v : VS k r 0 D E)
    (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    ((qminor (E0 (E := E) hD) a b u) v : Q.Mx k r → E) g = qminorOp (Q.EH k r) a b u (v : Q.Mx k r → E) g := by sorry
