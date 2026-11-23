-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_tb_congr
-- name    : Formalism.FourierDecayAlt.P.Jx9.tb_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:14.900115+00:00
-- url     : https://prove2.me/theorems/b79324ce-27d0-4491-84f0-3dcbb9b1dfb9
-- title:
--   Jx9: tb congr
-- statement:
--   The Jx9 construction uses the tb congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AxiomsFromFamilies.lean#L121-L126

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

theorem Formalism.FourierDecayAlt.P.Jx9.tb_congr {α : Type} {F : Finset α} {k k' : α → α → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y)
    (hk : TB.PSDOn F k) : TB.PSDOn F k' := by sorry
