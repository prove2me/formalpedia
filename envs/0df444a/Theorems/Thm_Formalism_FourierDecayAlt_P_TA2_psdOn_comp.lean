-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_psdOn_comp
-- name    : Formalism.FourierDecayAlt.P.TA2.psdOn_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:10.628346+00:00
-- url     : https://prove2.me/theorems/17ad0f69-b5e8-4c92-aa34-c8d2e078b72f
-- title:
--   TA2: psd On comp
-- statement:
--   The TA2 construction uses the psd On comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L72-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L72-L83

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

theorem Formalism.FourierDecayAlt.P.TA2.psdOn_comp {α β : Type} [DecidableEq β] (f : α → β) (g : β → α) (hg : ∀ x, g (f x) = x)
    (P : Finset α) (k : β → β → ℂ) (hk : PSDOn (P.image f) k) :
    PSDOn P (fun x y => k (f x) (f y)) := by sorry
