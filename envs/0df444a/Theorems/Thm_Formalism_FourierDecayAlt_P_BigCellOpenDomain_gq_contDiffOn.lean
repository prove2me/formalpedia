-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellOpenDomain_gq_contDiffOn
-- name    : Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:09:28.517364+00:00
-- url     : https://prove2.me/theorems/921ca3e4-9896-4877-91e2-5f1d5040eacf
-- title:
--   Big Cell Open Domain: gq cont Diff On
-- statement:
--   The Big Cell Open Domain construction uses the gq cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellOpenDomain.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellOpenDomain.lean#L44-L53

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellOpenDomain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn (D : RealPlaceData k r Wp Wq) (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q => gq D q) (QDom k r D.z D.z') := by sorry
