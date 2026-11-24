-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_fold_poly
-- name    : Formalism.FourierDecayAlt.P.Qx2.fold_poly
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:19:46.77098+00:00
-- url     : https://prove2.me/theorems/535e77fe-b94a-41e4-bffd-a486f489b669
-- title:
--   Qx2: fold poly
-- statement:
--   The Qx2 construction uses the fold poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L596-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L596-L615

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

theorem Formalism.FourierDecayAlt.P.Qx2.fold_poly (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f)
    (L : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) :
    PolyFam k r i D L.length (fun Y x => (L.map (opF k r i Y)).foldr (fun T h => T h) f x -
      Y ^ L.length • ((L.map (dl k r i)).prod • f x)) := by sorry
