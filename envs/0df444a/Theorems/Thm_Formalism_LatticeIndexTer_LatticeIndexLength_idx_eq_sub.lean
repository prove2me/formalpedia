-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_idx_eq_sub
-- name    : Formalism.LatticeIndexTer.LatticeIndexLength.idx_eq_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:31.824874+00:00
-- url     : https://prove2.me/theorems/85fa1e0f-74b6-4e3e-b8f4-c15e406507a3
-- title:
--   Lattice Index Length: idx eq sub
-- statement:
--   The Lattice Index Length construction uses the idx eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L126-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean#L126-L146

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength

theorem Formalism.LatticeIndexTer.LatticeIndexLength.idx_eq_sub {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (P Q D : Submodule O X) (hD : D ≤ P ⊓ Q)
    (hP : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤)
    (hQ : Module.length O (Q ⧸ D.comap Q.subtype) ≠ ⊤) :
    idx O X P Q = ((Module.length O (P ⧸ D.comap P.subtype)).toNat : ℤ) -
      ((Module.length O (Q ⧸ D.comap Q.subtype)).toNat : ℤ) := by sorry
