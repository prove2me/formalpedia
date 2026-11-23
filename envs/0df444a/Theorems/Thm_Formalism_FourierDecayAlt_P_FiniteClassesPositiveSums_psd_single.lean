-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_single
-- name    : Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:40.560722+00:00
-- url     : https://prove2.me/theorems/23e5d278-b068-4b59-8ec1-dec134c00817
-- title:
--   Finite Classes Positive Sums: psd single
-- statement:
--   The Finite Classes Positive Sums construction uses the psd single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L79-L100

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

theorem Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_single (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {M : Point K → Point K → ℂ} {Θ : K → Point K → Point K → ℂ}
    (h1 : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) (h2 : ∀ x, IsPSD F (Θ x))
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0)
    (h5 : IsPSD F (fun h h' => M h h' - ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h'))
    (x : K) : IsPSD F (fun h h' => M h h' - Θ x h h') := by sorry
