-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_small
-- name    : Formalism.FourierDecayAlt.P.A6x4.small
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:44:08.034358+00:00
-- url     : https://prove2.me/theorems/1fb4f3ae-7bc6-4045-abb8-cbc6cfb3471c
-- title:
--   A6x4: small
-- statement:
--   The A6x4 construction uses the small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L207-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L207-L232

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

theorem Formalism.FourierDecayAlt.P.A6x4.small (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hp : p ∈ R) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {V : Set K}
    (hV : V ∈ 𝓝 (0 : K)) : ∃ m : ℕ, ∀ x, q ^ m * x ∈ R → x ∈ V := by sorry
