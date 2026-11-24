-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_fib_core
-- name    : Formalism.FourierDecayAlt.P.A5x9.fib_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:56.065047+00:00
-- url     : https://prove2.me/theorems/66aebbbe-7d9c-44fb-8150-e2454895b31b
-- title:
--   A5x9: fib core
-- statement:
--   The A5x9 construction uses the fib core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1604-L1696
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1604-L1696

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
open Classical

theorem Formalism.FourierDecayAlt.P.A5x9.fib_core (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (w w' : Point K) (k : ℕ) (hn : w.1.sum = w'.1.sum) (hkn : k + 2 ≤ w.1.sum)
    (Q : Finset (Cos R w × Cos R w'))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) (y) (y')
    (he : ∀ a b : Fin w.1.sum, k < a.val → b.val + 1 = w.1.sum → (base R k w y)⁻¹ a b = 0)
    (he' : ∀ a b : Fin w'.1.sum, k < a.val → b.val + 1 = w'.1.sum →
      (base R k w' y')⁻¹ a b = 0) :
    ∑ q ∈ Q with (kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      (badN R k w w' q : ℂ) * (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by sorry
