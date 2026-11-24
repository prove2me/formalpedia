-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_cut_supp
-- name    : Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.cut_supp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:12:54.050814+00:00
-- url     : https://prove2.me/theorems/001a7932-bdb8-4c00-8705-cc67ea915a73
-- title:
--   Differential Operator Classes: cut supp
-- statement:
--   The Differential Operator Classes construction uses the cut supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L134-L141

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.cut_supp (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (χ₀ : ℝ → ℝ) (de : ℝ) (L : Finset (Fin (r + 2)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ g ∈ B.GV k r, C6.cutAll D χ₀ de L F g ≠ 0 → ε ≤ Gf k r D.z D.z' g := by sorry
