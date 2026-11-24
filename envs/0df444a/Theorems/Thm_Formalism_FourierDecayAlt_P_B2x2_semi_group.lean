-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_semi_group
-- name    : Formalism.FourierDecayAlt.P.B2x2.semi_group
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:56:43.541817+00:00
-- url     : https://prove2.me/theorems/09a1d695-9ed1-4522-ae6c-93f5c4cd165b
-- title:
--   B2x2: semi group
-- statement:
--   The B2x2 construction uses the semi group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L552-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L552-L568

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2

theorem Formalism.FourierDecayAlt.P.B2x2.semi_group {k r : ℕ} (A B : Set (Mat k r)) (hA : IsClosedSubgroup A) (hB : IsClosedSubgroup B)
    (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hcl : IsClosed (mulSet A B)) : IsClosedSubgroup (mulSet A B) := by sorry
