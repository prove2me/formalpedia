-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_primeDvdChooseIff
-- name    : Formalism.IncomingBounds.primeDvdChooseIff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:51.501125+00:00
-- url     : https://prove2.me/theorems/39ac7dbe-3303-41be-ac68-7f9a13daca30
-- title:
--   Incoming Bounds: prime Dvd Choose Iff
-- statement:
--   The Incoming Bounds construction uses the prime Dvd Choose Iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L59-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ProdRangeEqFactorialMulProdIco.lean#L59-L100

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.primeDvdChooseIff : BinomGcd := by sorry
