-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_std
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_mem_std
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:58:38.140316+00:00
-- url     : https://prove2.me/theorems/7e097864-6bb8-4ead-bcc0-c19d419842e3
-- title:
--   Column Families: qb mem std
-- statement:
--   The Column Families construction uses the qb mem std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L42-L55

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_mem_std (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (x : M.ι → ℤ) (h : ∀ mu, Dominant mu → mu ∉ pi → qb_ev M ℚ mu (fun i => (x i : ℚ)) = 0) :
    x ∈ Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} := by sorry
