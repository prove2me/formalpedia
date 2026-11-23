-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W8_arith_fact_top
-- name    : Formalism.DivisionValues.W8.arith_fact_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:43.246819+00:00
-- url     : https://prove2.me/theorems/b5d06e24-a26a-40d2-92af-1694e0054022
-- title:
--   W8: arith fact top
-- statement:
--   The W8 construction uses the arith fact top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L432-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L432-L447

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open W8
open Formalism.DivisionValues.W8

theorem Formalism.DivisionValues.W8.arith_fact_top {w S Sc N Bl cs C0 La n k : ℝ} (hw : 0 ≤ w) (hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hk : k = n + 2) (hkN : k ≤ N) (hcs : 0 ≤ cs) (hC2 : 2 ≤ C0) (hCcs : cs + 1 ≤ C0)
    (hSc : 2 * Sc ≤ C0 * S) (hLa : 1 ≤ La) :
    (2 * w + Sc + n * (cs * N) + Bl) * La + 1 ≤ C0 * (w + S + N ^ 2 + Bl) * La := by sorry
