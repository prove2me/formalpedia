-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_arith
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:35.510833+00:00
-- url     : https://prove2.me/theorems/b25fe72a-062e-4199-ac72-5027ec188e7c
-- title:
--   Lattice Index Determinant: arith
-- statement:
--   The Lattice Index Determinant construction uses the arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L33-L47

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

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.arith (x y d va vb ve ve' : ℕ∞) (h1 : ve = x + d) (h2 : ve' = y + d)
    (h3 : ve + vb = ve' + va) (hve : ve ≠ ⊤) (hve' : ve' ≠ ⊤) (hva : va ≠ ⊤) (hvb : vb ≠ ⊤) :
    (x.toNat : ℤ) - y.toNat = va.toNat - vb.toNat := by sorry
