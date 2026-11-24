-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_orbJ_congr
-- name    : Formalism.FourierDecayAlt.P.TBBx2.orbJ_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:12.778574+00:00
-- url     : https://prove2.me/theorems/7b025c9a-d096-4058-9284-bc24fb04204d
-- title:
--   TBBx2: orb J congr
-- statement:
--   The TBBx2 construction uses the orb J congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L20-L33

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.TBBx2.orbJ_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)) (F G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hae : ∀ᵐ q ∂Ds.μSS, D.orbIntegrand Ds γ F q = D.orbIntegrand Ds γ G q) :
    D.orbJ Ds γ μR F = D.orbJ Ds γ μR G := by sorry
