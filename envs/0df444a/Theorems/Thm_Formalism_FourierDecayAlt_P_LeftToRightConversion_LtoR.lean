-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_LtoR
-- name    : Formalism.FourierDecayAlt.P.LeftToRightConversion.LtoR
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:23.209936+00:00
-- url     : https://prove2.me/theorems/f8e1e3d6-7199-4eb4-80e8-f35a50dce2c7
-- title:
--   Left To Right Conversion: Lto R
-- statement:
--   The Left To Right Conversion construction uses the Lto R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L84-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L84-L145

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.LeftToRightConversion.LtoR : ∀ u : List (Mat k r), (∀ X ∈ u, inLie k r X) →
    ∃ L : List ((Mat k r → ℂ) × List (Mat k r)),
      (∀ p ∈ L, PolyClass (2 * u.length) p.1 ∧ p.2.length ≤ u.length ∧ ∀ Y ∈ p.2, unitLie k r Y) ∧
      ∀ H : Mat k r → E, CkOn ((u.length : ℕ) : ℕ∞) (GV k r) H → ∀ g ∈ GV k r,
        u.foldr LdV H g = (L.map fun p => p.1 g • Rw p.2 H g).sum := by sorry
