-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_mem_span_standard_iff_proj_zero
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.mem_span_standard_iff_proj_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:58:44.587023+00:00
-- url     : https://prove2.me/theorems/a11f6765-efd3-480e-9ada-5234b1f330a4
-- title:
--   Column Families: mem span standard iff proj zero
-- statement:
--   The Column Families construction uses the mem span standard iff proj zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L22-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/MemSpanStandardIffProjZero.lean#L22-L40

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.mem_span_standard_iff_proj_zero (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (F : Type) [Field F] (x : M.ι → F) :
    x ∈ Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ y = fun i => (CF.vec j I i : F)} ↔
      ∀ mu, Dominant mu → mu ∉ pi → qb_ev M F mu x = 0 := by sorry
