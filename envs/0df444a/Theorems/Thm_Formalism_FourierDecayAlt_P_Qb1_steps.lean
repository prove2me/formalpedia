-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_steps
-- name    : Formalism.FourierDecayAlt.P.Qb1.steps
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:20:45.494713+00:00
-- url     : https://prove2.me/theorems/8b374f33-6b5c-480a-9629-a3af6abb9a9a
-- title:
--   Qb1: steps
-- statement:
--   The Qb1 construction uses the steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L142-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L142-L156

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

theorem Formalism.FourierDecayAlt.P.Qb1.steps (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) :
    ∀ (L : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (w : Vs), SV σ w →
      SV σ (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w) ∧
      ∀ g ∈ GV k r, (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 p.2.1 p.2.2).foldr (fun T h => T h) (fun x => ℓ (σ x w)) g =
        ℓ (σ g (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w)) := by sorry
