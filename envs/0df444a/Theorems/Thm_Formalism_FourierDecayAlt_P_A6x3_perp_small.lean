-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_small
-- name    : Formalism.FourierDecayAlt.P.A6x3.perp_small
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:22.927916+00:00
-- url     : https://prove2.me/theorems/a7bc1bbe-c188-4abb-942c-a64f18f5eec7
-- title:
--   A6x3: perp small
-- statement:
--   The A6x3 construction uses the perp small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L299-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L299-L324

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x3.perp_small (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    {L : AddSubgroup K} (hL : Lat L) (hLR : L ≤ R.toAddSubgroup) :
    Lat (perp ψ L) ∧ perp ψ (perp ψ L) = L ∧ volL R L * volL R (perp ψ L) = 1 := by sorry
