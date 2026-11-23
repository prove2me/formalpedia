-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_gram_nonneg
-- name    : Formalism.FourierDecayAlt.P.TA2.gram_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:56.421188+00:00
-- url     : https://prove2.me/theorems/c4eed95d-4036-483f-9e4f-373403e0cae9
-- title:
--   TA2: gram nonneg
-- statement:
--   The TA2 construction uses the gram nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L44-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L44-L70

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2

theorem Formalism.FourierDecayAlt.P.TA2.gram_nonneg {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (k : α → α → ℂ) (V : α → H) (hk : PSDOn P k) :
    0 ≤ (∑ x ∈ P, ∑ y ∈ P, k x y * ⟪V x, V y⟫_ℂ).re := by sorry
