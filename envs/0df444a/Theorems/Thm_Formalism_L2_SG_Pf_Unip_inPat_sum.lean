-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sum
-- name    : Formalism.L2.SG.Pf.Unip.inPat_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:57.284723+00:00
-- url     : https://prove2.me/theorems/b77aff8a-fcd2-4df3-8409-1517cabd1706
-- title:
--   Unip: in Pat sum
-- statement:
--   The Unip construction uses the in Pat sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L64-L68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}

theorem Formalism.L2.SG.Pf.Unip.inPat_sum {α : Type*} {s : Finset α} {f : α → Matrix ι ι K} (h : ∀ a ∈ s, InPat lv k (f a)) :
    InPat lv k (∑ a ∈ s, f a) := by sorry
