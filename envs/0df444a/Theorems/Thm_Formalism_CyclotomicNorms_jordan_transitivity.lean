-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_jordan_transitivity
-- name    : Formalism.CyclotomicNorms.jordan_transitivity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:28.869325+00:00
-- url     : https://prove2.me/theorems/7b8dece7-8c08-4a00-968f-59e4d31def8f
-- title:
--   Cyclotomic Norms: jordan transitivity
-- statement:
--   The Cyclotomic Norms construction uses the jordan transitivity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Jordan.lean#L97-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Jordan.lean#L97-L118

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Jordan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms

theorem Formalism.CyclotomicNorms.jordan_transitivity : JordanTransitive := by sorry
