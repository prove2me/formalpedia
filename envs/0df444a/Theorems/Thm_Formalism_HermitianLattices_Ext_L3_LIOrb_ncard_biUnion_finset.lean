-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_ncard_biUnion_finset
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.ncard_biUnion_finset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:10.932205+00:00
-- url     : https://prove2.me/theorems/e0830685-4dc3-4111-a079-2409bc633252
-- title:
--   LIOrb: ncard bi Union finset
-- statement:
--   The LIOrb construction uses the ncard bi Union finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfCover.lean#L84-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfCover.lean#L84-L100

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
open Subgroup
variable {G : Type*} [Group G]

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.ncard_biUnion_finset {ι X : Type*} (s : Finset ι) (f : ι → Set X)
    (hf : ∀ i ∈ s, (f i).Finite) (hd : (s : Set ι).PairwiseDisjoint f) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by sorry
