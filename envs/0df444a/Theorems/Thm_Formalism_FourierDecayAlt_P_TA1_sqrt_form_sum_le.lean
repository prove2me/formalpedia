-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_sqrt_form_sum_le
-- name    : Formalism.FourierDecayAlt.P.TA1.sqrt_form_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:56.96218+00:00
-- url     : https://prove2.me/theorems/3790bc57-0775-4597-87ce-77989ec6a987
-- title:
--   TA1: sqrt form sum le
-- statement:
--   The TA1 construction uses the sqrt form sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagonalTopBlock.lean#L58-L64

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.TA1.sqrt_form_sum_le (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) {ι : Type} (T : Finset ι)
    (U : ι → α → H) :
    √(form P k (∑ s ∈ T, U s) (∑ s ∈ T, U s)).re ≤ ∑ s ∈ T, √(form P k (U s) (U s)).re := by sorry
