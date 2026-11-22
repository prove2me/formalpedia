-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_image_pow_eq_preimage
-- name    : Formalism.FourierDecayAlt.P.A6x5.image_pow_eq_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:56.141547+00:00
-- url     : https://prove2.me/theorems/72e63262-17bc-41ff-9945-d036d4759ac1
-- title:
--   A6x5: image pow eq preimage
-- statement:
--   The A6x5 construction uses the image pow eq preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L170-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L170-L182

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x5.image_pow_eq_preimage (ϖ : Kˣ) (N : ℕ) (S : Set K) :
    (fun r => (ϖ : K) ^ N * r) '' S = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) ⁻¹' S := by sorry
