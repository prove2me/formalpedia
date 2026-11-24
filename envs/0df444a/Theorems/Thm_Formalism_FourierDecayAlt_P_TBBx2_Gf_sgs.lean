-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Gf_sgs
-- name    : Formalism.FourierDecayAlt.P.TBBx2.Gf_sgs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:23.475275+00:00
-- url     : https://prove2.me/theorems/8f3b2a65-0c02-4f60-8682-48dc143cd1ee
-- title:
--   TBBx2: Gf sgs
-- statement:
--   The TBBx2 construction uses the Gf sgs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L41-L59

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

theorem Formalism.FourierDecayAlt.P.TBBx2.Gf_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) (q : B.SS k r)
    (hq : Ds.inSS q) (g : B.Mat k r) :
    Gf k r Ds.z Ds.z' (B.sgs q g) = Gf k r Ds.z Ds.z' g := by sorry
