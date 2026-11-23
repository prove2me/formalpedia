-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_one_add
-- name    : Formalism.FourierDecayAlt.P.A6x4.one_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:36.939801+00:00
-- url     : https://prove2.me/theorems/dcf19041-cbde-4c57-ba4d-1f982ee25fca
-- title:
--   A6x4: one add
-- statement:
--   The A6x4 construction uses the one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L234-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L234-L285

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x4.one_add (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hp : p ∈ R) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {x : K} (hx : x ∈ R) :
    ∃ w : K, (1 + p * x) * w = 1 ∧ 1 + p * x ∈ R ∧ w ∈ R := by sorry
