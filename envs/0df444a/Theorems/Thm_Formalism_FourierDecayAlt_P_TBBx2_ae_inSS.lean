-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_ae_inSS
-- name    : Formalism.FourierDecayAlt.P.TBBx2.ae_inSS
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:23.528107+00:00
-- url     : https://prove2.me/theorems/5dbc99ae-1984-4d48-b508-a5a7d0585fff
-- title:
--   TBBx2: ae in SS
-- statement:
--   The TBBx2 construction uses the ae in SS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L61-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L61-L92

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

theorem Formalism.FourierDecayAlt.P.TBBx2.ae_inSS {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) :
    ∀ᵐ q ∂Ds.μSS, Ds.inSS q := by sorry
