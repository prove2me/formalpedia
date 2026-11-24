-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellOpenDomain_mu_entry
-- name    : Formalism.FourierDecayAlt.P.BigCellOpenDomain.mu_entry
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:09:44.920809+00:00
-- url     : https://prove2.me/theorems/41747e28-c31e-44f9-976b-7325ac8a3bff
-- title:
--   Big Cell Open Domain: mu entry
-- statement:
--   The Big Cell Open Domain construction uses the mu entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellOpenDomain.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellOpenDomain.lean#L39-L42

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

theorem Formalism.FourierDecayAlt.P.BigCellOpenDomain.mu_entry (D : RealPlaceData k r Wp Wq) (n : ℕ) (a b : Fin (k + 1)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => D.μsec q.2 a b) (QDom k r D.z D.z') := by sorry
