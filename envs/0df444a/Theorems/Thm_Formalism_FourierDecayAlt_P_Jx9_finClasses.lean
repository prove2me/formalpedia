-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_finClasses
-- name    : Formalism.FourierDecayAlt.P.Jx9.finClasses
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:20.285229+00:00
-- url     : https://prove2.me/theorems/c7b9f734-443d-48f7-8663-3545438cc051
-- title:
--   Jx9: fin Classes
-- statement:
--   The Jx9 construction uses the fin Classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L106-L119

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9

theorem Formalism.FourierDecayAlt.P.Jx9.finClasses {X K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (hR : IsOpen (R : Set K)) (F' : Finset X) (Θ : K → X → X → ℂ)
    (h3 : ∃ L : Submodule R K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
      ∀ x, x ∉ L → ∀ h ∈ F', ∀ h' ∈ F', Θ x h h' = 0) :
    {x : K ⧸ R.toAddSubgroup | ∃ h ∈ F', ∃ h' ∈ F', Θ (Quotient.out x) h h' ≠ 0}.Finite := by sorry
