-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_preimage_pow_eq_image
-- name    : Formalism.FourierDecayAlt.P.A6x5.preimage_pow_eq_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:34.868659+00:00
-- url     : https://prove2.me/theorems/f2b8e352-1694-49df-ae0a-78898a9f1d4f
-- title:
--   A6x5: preimage pow eq image
-- statement:
--   The A6x5 construction uses the preimage pow eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L184-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L184-L188

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

theorem Formalism.FourierDecayAlt.P.A6x5.preimage_pow_eq_image (ϖ : Kˣ) (N : ℕ) (S : Set K) :
    (fun x => (ϖ : K) ^ N * x) ⁻¹' S = (fun r => ((ϖ⁻¹ : Kˣ) : K) ^ N * r) '' S := by sorry
