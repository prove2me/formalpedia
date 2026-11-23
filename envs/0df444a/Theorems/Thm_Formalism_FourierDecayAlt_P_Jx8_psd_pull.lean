-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_pull
-- name    : Formalism.FourierDecayAlt.P.Jx8.psd_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:53.772794+00:00
-- url     : https://prove2.me/theorems/a9ebfb55-1989-4e89-a658-934d3a12016c
-- title:
--   Jx8: psd pull
-- statement:
--   The Jx8 construction uses the psd pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L350-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L350-L355

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8

theorem Formalism.FourierDecayAlt.P.Jx8.psd_pull {α β : Type} {G : Finset β} {F : Finset α} (f : G → F) {k : α → α → ℂ}
    {k' : β → β → ℂ} (h : ∀ x y : G, k' x y = k (f x) (f y)) (hk : TB.PSDOn F k) : TB.PSDOn G k' := by sorry
