-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_product_of_energies
-- name    : Formalism.FourierDecayAlt.P.product_of_energies
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:34:27.223698+00:00
-- url     : https://prove2.me/theorems/4bc32817-e644-4bc9-a4d1-31f82f518dce
-- title:
--   P: product of energies
-- statement:
--   The P construction uses the product of energies property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionGivesUniformBoundsForm.lean#L123-L126

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx6

theorem Formalism.FourierDecayAlt.P.product_of_energies : Formalism.FourierDecayAlt.J.ProductOfE := by sorry
