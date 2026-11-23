-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FinitePointSets_rows_le_form
-- name    : Formalism.FourierDecayAlt.P.FinitePointSets.rows_le_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:14.691593+00:00
-- url     : https://prove2.me/theorems/c6f185d1-5210-4e21-b6c8-fc2d80c4887c
-- title:
--   Finite Point Sets: rows le form
-- statement:
--   The Finite Point Sets construction uses the rows le form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinitePointSets.lean#L91-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinitePointSets.lean#L91-L107

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinitePointSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FinitePointSets
open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

theorem Formalism.FourierDecayAlt.P.FinitePointSets.rows_le_form {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (V : α → H) (c : ℕ → α → ℂ) (R : Finset ℕ)
    (h : PSDOn Y (fun p q => k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q))) :
    ∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by sorry
