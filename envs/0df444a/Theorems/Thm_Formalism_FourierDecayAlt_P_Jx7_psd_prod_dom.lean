-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_prod_dom
-- name    : Formalism.FourierDecayAlt.P.Jx7.psd_prod_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:25.699243+00:00
-- url     : https://prove2.me/theorems/e40d4e87-0646-4956-801b-aef60c5a915b
-- title:
--   Jx7: psd prod dom
-- statement:
--   The Jx7 construction uses the psd prod dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L856-L871
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L856-L871

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
variable {α : Type} {F : Finset α}

theorem Formalism.FourierDecayAlt.P.Jx7.psd_prod_dom {P : Type} (s : Finset P) (k K : P → α → α → ℂ) (hk : ∀ p ∈ s, TB.PSDOn F (k p))
    (hd : ∀ p ∈ s, TB.PSDOn F (fun x y => K p x y - k p x y)) :
    TB.PSDOn F (fun x y => ∏ p ∈ s, K p x y - ∏ p ∈ s, k p x y) := by sorry
