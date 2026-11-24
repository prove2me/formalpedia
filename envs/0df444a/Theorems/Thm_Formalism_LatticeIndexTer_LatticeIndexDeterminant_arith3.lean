-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_arith3
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.arith3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:24.957005+00:00
-- url     : https://prove2.me/theorems/3b80c99d-1be6-482f-b1a2-4887a6319660
-- title:
--   Lattice Index Determinant: arith3
-- statement:
--   The Lattice Index Determinant construction uses the arith3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L49-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L49-L64

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.arith3 (p q p1 q1 p2 q2 p3 q3 : ℕ∞) (h : p + (q1 + q2 + q3) = q + (p1 + p2 + p3))
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : p1 ≠ ⊤) (hq1 : q1 ≠ ⊤) (hp2 : p2 ≠ ⊤) (hq2 : q2 ≠ ⊤)
    (hp3 : p3 ≠ ⊤) (hq3 : q3 ≠ ⊤) :
    (p.toNat : ℤ) - q.toNat =
      ((p1.toNat : ℤ) - q1.toNat) + ((p2.toNat : ℤ) - q2.toNat) + ((p3.toNat : ℤ) - q3.toNat) := by sorry
