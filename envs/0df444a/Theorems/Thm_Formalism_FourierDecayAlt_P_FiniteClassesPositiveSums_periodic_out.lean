-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_periodic_out
-- name    : Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.periodic_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:37.649805+00:00
-- url     : https://prove2.me/theorems/0080811e-7abb-452d-a9e9-b0c53dcdfaa2
-- title:
--   Finite Classes Positive Sums: periodic out
-- statement:
--   The Finite Classes Positive Sums construction uses the periodic out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteClassesPositiveSums.lean#L53-L56

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

theorem Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.periodic_out {β : Type} (f : K → β) (h1 : ∀ x, ∀ r ∈ R, f (x + r) = f x) (x : K) :
    f (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = f x := by sorry
