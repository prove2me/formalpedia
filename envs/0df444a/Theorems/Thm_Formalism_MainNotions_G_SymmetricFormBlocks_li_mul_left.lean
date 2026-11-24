-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_SymmetricFormBlocks_li_mul_left
-- name    : Formalism.MainNotions.G.SymmetricFormBlocks.li_mul_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:55:18.979355+00:00
-- url     : https://prove2.me/theorems/476acea0-ee7c-4841-8bf7-4888705574d5
-- title:
--   Symmetric Form Blocks: li mul left
-- statement:
--   The Symmetric Form Blocks construction uses the li mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialFactorials/LiRenameMon.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialFactorials/LiRenameMon.lean#L57-L67

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiRenameMon
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open MvPolynomial Finset Formalism.GM.M.SSD
variable {σ τ K : Type} [Field K] [DecidableEq σ] (e : τ → σ) (he : Function.Injective e)
set_option maxHeartbeats 800000

theorem Formalism.MainNotions.G.SymmetricFormBlocks.li_mul_left {ι : Type} (F : MvPolynomial σ K) (hF : F ≠ 0) (v : ι → MvPolynomial σ K) (hv : LinearIndependent K v) :
    LinearIndependent K (fun i => F * v i) := by sorry
