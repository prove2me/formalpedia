-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_prod
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.LW.prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:01.812024+00:00
-- url     : https://prove2.me/theorems/894b1ee2-558f-4b4c-ab27-87d59dab3e0d
-- title:
--   LW: prod
-- statement:
--   The LW construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L666-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L666-L673

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.LW.prod {ι : Type} (s : Finset ι) {f : ι → (Fin m → K) → K} (hf : ∀ i, LW R c (f i)) :
    LW R c (fun v => ∏ i ∈ s, f i v) := by sorry
