-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_pow_eq_zero_of_le
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.pow_eq_zero_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:18.0578+00:00
-- url     : https://prove2.me/theorems/96f1f2e6-8610-41d2-aa45-5dd23d0adaa3
-- title:
--   Hermitian Projections: pow eq zero of le
-- statement:
--   The Hermitian Projections construction uses the pow eq zero of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L115-L118

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections

theorem Formalism.FourierDecayAlt.P.HermitianProjections.pow_eq_zero_of_le {R : Type*} [MonoidWithZero R] {x : R} {p q : ℕ} (h : x ^ p = 0)
    (hpq : p ≤ q) : x ^ q = 0 := by sorry
