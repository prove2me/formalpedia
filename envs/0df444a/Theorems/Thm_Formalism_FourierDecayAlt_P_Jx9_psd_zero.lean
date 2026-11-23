-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_zero
-- name    : Formalism.FourierDecayAlt.P.Jx9.psd_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:22.592953+00:00
-- url     : https://prove2.me/theorems/848ef76e-c2b2-4ec4-b97e-5510c9f861c6
-- title:
--   Jx9: psd zero
-- statement:
--   The Jx9 construction uses the psd zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L18-L19

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
variable {α X : Type}

theorem Formalism.FourierDecayAlt.P.Jx9.psd_zero (F : Finset α) : A5.IsPSD F (fun _ _ => (0 : ℂ)) := by sorry
