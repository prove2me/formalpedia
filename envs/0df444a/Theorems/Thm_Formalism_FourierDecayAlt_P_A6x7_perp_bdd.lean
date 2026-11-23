-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_perp_bdd
-- name    : Formalism.FourierDecayAlt.P.A6x7.perp_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:07.400908+00:00
-- url     : https://prove2.me/theorems/ec91fee8-9850-411c-a31a-2c2a88b64264
-- title:
--   A6x7: perp bdd
-- statement:
--   The A6x7 construction uses the perp bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L148-L156

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x7.perp_bdd (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (L : AddSubgroup K)
    (hL : IsLat L) : ∃ C : Set K, IsCompact C ∧ ∀ y ∈ perp ψ L, y ∈ C := by sorry
