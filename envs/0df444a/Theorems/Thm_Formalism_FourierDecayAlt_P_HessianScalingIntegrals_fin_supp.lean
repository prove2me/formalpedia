-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_fin_supp
-- name    : Formalism.FourierDecayAlt.P.HessianScalingIntegrals.fin_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:12.274309+00:00
-- url     : https://prove2.me/theorems/6855b157-4a7a-4f5d-9f85-9df998c49aa9
-- title:
--   Hessian Scaling Integrals: fin supp
-- statement:
--   The Hessian Scaling Integrals construction uses the fin supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L16-L24

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.HessianScalingIntegrals.fin_supp [TopologicalSpace K] [IsTopologicalRing K] (Λ L : AddSubgroup K)
    (hΛ : IsOpen (Λ : Set K)) (hL : IsCompact (L : Set K)) (d : ℕ) :
    {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite := by sorry
