-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_diff_of_pres
-- name    : Formalism.FourierDecayAlt.P.NFx1.TC.diff_of_pres
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:48.084247+00:00
-- url     : https://prove2.me/theorems/9d440cad-f779-469f-b915-3e65f43a2aa3
-- title:
--   TC: diff of pres
-- statement:
--   The TC construction uses the diff of pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L477-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L477-L482

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx1 Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}

theorem Formalism.FourierDecayAlt.P.NFx1.TC.diff_of_pres {T : (Mx k r → E) → Mx k r → E}
    (hp : ∀ (U₀ : Set ((Fin r → ℂ) × Mx k r)) (Φ : Fn k r E), SmoothFam k r i U₀ Φ →
      SmoothFam k r i U₀ (fun c => T (Φ c)))
    {U₀ : Set ((Fin r → ℂ) × Mx k r)} {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) {x : (Fin r → ℂ) × Mx k r}
    (hx : x ∈ U₀) (hg : x.2 ∈ Glev k r i) : DifferentiableAt ℝ (fun c' => T (Φ c') x.2) x.1 := by sorry
