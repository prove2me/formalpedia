-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_fibre_zero
-- name    : Formalism.FourierDecayAlt.P.A5x9.fibre_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:09.579724+00:00
-- url     : https://prove2.me/theorems/70435cdd-78d2-47d6-9458-e78e5d9e64c4
-- title:
--   A5x9: fibre zero
-- statement:
--   The A5x9 construction uses the fibre zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1700-L1718
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1700-L1718

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

theorem Formalism.FourierDecayAlt.P.A5x9.fibre_zero (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (h h' : Point K) (s : ℕ) (t t' : Kˣ) (k : ℕ) (hh : h.1.sum = h'.1.sum) (hk : h.1.sum ≤ k)
    (hks : k + 2 ≤ h.1.sum + s)
    (Q : Finset (Cos R (addBlock h s t) × Cos R (addBlock h' s t')))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2))) (y) (y') :
    ∑ q ∈ Q with (kap R k (addBlock h s t) q.1 = y ∧ kap R k (addBlock h' s t') q.2 = y'),
      (badN R k (addBlock h s t) (addBlock h' s t') q : ℂ) *
        (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by sorry
