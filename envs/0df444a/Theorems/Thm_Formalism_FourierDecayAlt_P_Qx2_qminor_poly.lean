-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_qminor_poly
-- name    : Formalism.FourierDecayAlt.P.Qx2.qminor_poly
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:16:20.823135+00:00
-- url     : https://prove2.me/theorems/11698ba5-5354-4fe4-98bd-fb25295439f0
-- title:
--   Qx2: qminor poly
-- statement:
--   The Qx2 construction uses the qminor poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L678-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L678-L703

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.Qx2.qminor_poly (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (s : ℂ) :
    PolyAt t (fun Y => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) (Y + s) f x -
      Y ^ t • (lc k r i a b • f x)) := by sorry
