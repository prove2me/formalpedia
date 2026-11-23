-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_isPt_PT
-- name    : Formalism.FourierDecayAlt.P.TA2.isPt_PT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:07.18828+00:00
-- url     : https://prove2.me/theorems/0020778a-9b29-428d-b790-fba960e09716
-- title:
--   TA2: is Pt PT
-- statement:
--   The TA2 construction uses the is Pt PT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L8-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L8-L30

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

theorem Formalism.FourierDecayAlt.P.TA2.isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by sorry
