-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_SymmetricFormBlocks_li_map
-- name    : Formalism.MainNotions.G.SymmetricFormBlocks.li_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:56.838591+00:00
-- url     : https://prove2.me/theorems/d0836b7a-fa21-4592-b99d-270c1bebdad3
-- title:
--   Symmetric Form Blocks: li map
-- statement:
--   The Symmetric Form Blocks construction uses the li map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialFactorials/LiMap.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialFactorials/LiMap.lean#L7-L30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open MvPolynomial

theorem Formalism.MainNotions.G.SymmetricFormBlocks.li_map {k L : Type*} [Field k] [Field L] (ι : k →+* L) {σ κ : Type*} (f : κ → MvPolynomial σ k)
    (hf : LinearIndependent k f) : LinearIndependent L (fun i => MvPolynomial.map ι (f i)) := by sorry
