-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W8_arith_per
-- name    : Formalism.DivisionValues.W8.arith_per
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:16.056116+00:00
-- url     : https://prove2.me/theorems/e3688515-f8ac-4f9d-b221-4446035b70b5
-- title:
--   W8: arith per
-- statement:
--   The W8 construction uses the arith per property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L462-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L462-L478

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

theorem Formalism.DivisionValues.W8.arith_per {d w S Sc N Bl C0 n k X : ℝ} (hw : 0 ≤ w) (hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hnk : n ≤ k) (hkN : k ≤ N) (hC2 : 2 ≤ C0) (hSc : 2 * Sc ≤ C0 * S) (hX : 0 ≤ X)
    (h1 : -w ≤ d) (h2 : d ≤ n * Sc + Bl) :
    |d| ≤ C0 * (w + k * (N + S) + Bl + X) := by sorry
