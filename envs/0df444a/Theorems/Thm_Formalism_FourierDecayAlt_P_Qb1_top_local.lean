-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_top_local
-- name    : Formalism.FourierDecayAlt.P.Qb1.top_local
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:20:54.281008+00:00
-- url     : https://prove2.me/theorems/cf1ee02c-c545-4f68-982f-47b8bcb683c6
-- title:
--   Qb1: top local
-- statement:
--   The Qb1 construction uses the top local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L135-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L135-L140

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem Formalism.FourierDecayAlt.P.Qb1.top_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (c : ℂ) (a b : Fin (2 * r + k + 1)) {g : Mx k r} (hg : g ∈ GV k r) :
    QuantumDeterminants.Top (EH k r) c a b f g = QuantumDeterminants.Top (EH k r) c a b f' g := by sorry
