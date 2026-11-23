-- Prove2me | Theorems.Thm_Formalism_HN_exists_smul_mem_of_finrank_eq
-- name    : Formalism.HN.exists_smul_mem_of_finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:42.701797+00:00
-- url     : https://prove2.me/theorems/3e66c53f-83c9-43ee-9ddc-538292616a2a
-- title:
--   HN: exists smul mem of finrank eq
-- statement:
--   The HN construction uses the exists smul mem of finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ExistsSmulMemOfFinrankEq.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ExistsSmulMemOfFinrankEq.lean#L11-L23

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
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
open Formalism Formalism.HN

theorem Formalism.HN.exists_smul_mem_of_finrank_eq {E : Type*} [AddCommGroup E] (S N : Submodule ℤ E) [Module.Finite ℤ S]
    (hNS : N ≤ S) (hrk : finrank ℤ S = finrank ℤ N) :
    ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N := by sorry
