-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_top_intTT_eq
-- name    : Formalism.FourierDecayAlt.P.A5x9.top_intTT_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:29.821223+00:00
-- url     : https://prove2.me/theorems/760a122f-1da6-4add-8d97-68570b71fbd3
-- title:
--   A5x9: top int TT eq
-- statement:
--   The A5x9 construction uses the top int TT eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1772-L1790
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1772-L1790

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x9.top_intTT_eq (ψ : AddChar K ℂ) (k₁ : ℕ) (w w' : Point K)
    (Q : Finset (Cos R w × Cos R w'))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) :
    intTT R ψ k₁ w w' = ∑ q ∈ Q,
      (Nat.card {φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
        φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
        InTT R k₁ (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ} : ℂ) *
      (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) := by sorry
