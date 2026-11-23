-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_limit_core
-- name    : Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.limit_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:45.410464+00:00
-- url     : https://prove2.me/theorems/f4d90fbd-f57e-4429-bb15-edac32edebdb
-- title:
--   Finite Classes Positive Sums: limit core
-- statement:
--   The Finite Classes Positive Sums construction uses the limit core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L102-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L102-L158

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
variable {K : Type} [CommRing K] (R : Subring K)
variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}

theorem Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.limit_core (hEntry : PSDEntryBound) (hSubseq : BoundedSubseq)
    (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    (M : Point K → Point K → ℂ) (Th : ℕ → K → Point K → Point K → ℂ)
    (h1 : ∀ j x, ∀ r ∈ R, Th j (x + r) = Th j x) (h2 : ∀ j x, IsPSD F (Th j x))
    (h3 : ∀ j x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Th j x h h' = 0)
    (h5 : ∀ j, IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th j (Quotient.out y) h h')) :
    ∃ (φ : ℕ → ℕ) (Θ : K → Point K → Point K → ℂ), StrictMono φ ∧
      (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
      ∀ x, ∀ h ∈ F, ∀ h' ∈ F, Tendsto (fun j => Th (φ j) x h h') atTop (𝓝 (Θ x h h')) := by sorry
