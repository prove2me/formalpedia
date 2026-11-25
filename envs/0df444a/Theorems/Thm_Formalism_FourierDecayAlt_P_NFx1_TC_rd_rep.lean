-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_rd_rep
-- name    : Formalism.FourierDecayAlt.P.NFx1.TC.rd_rep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:22:00.848114+00:00
-- url     : https://prove2.me/theorems/a6a17d96-955a-4c4e-949a-02d65a5ab041
-- title:
--   TC: rd rep
-- statement:
--   The TC construction uses the rd rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L529-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L529-L550

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

theorem Formalism.FourierDecayAlt.P.NFx1.TC.rd_rep {Φ : Fn k r E} {U : Set ((Fin r → ℂ) × Mx k r)} {F : (Fin r → ℂ) × Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ y ∈ U, y.2 ∈ Glev k r i → Φ y.1 y.2 = F y)
    {X : Mx k r} (hX : inLieLev k r i X) {y : (Fin r → ℂ) × Mx k r} (hy : y ∈ U) (hyG : y.2 ∈ Glev k r i) :
    RdV X (Φ y.1) y.2 = fderiv ℝ F y ((0 : Fin r → ℂ), y.2 * X) := by sorry
