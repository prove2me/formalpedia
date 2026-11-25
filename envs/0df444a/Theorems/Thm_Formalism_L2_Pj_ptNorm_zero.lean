-- Prove2me | Theorems.Thm_Formalism_L2_Pj_ptNorm_zero
-- name    : Formalism.L2.Pj.ptNorm_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:46:22.811897+00:00
-- url     : https://prove2.me/theorems/36b3de06-84c0-495f-969d-0bfbcf89161a
-- title:
--   Pj: pt Norm zero
-- statement:
--   The Pj construction uses the pt Norm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L134-L137

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPolynomial
variable {K : Type} [Field K]
variable {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

theorem Formalism.L2.Pj.ptNorm_zero (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (y : pts (CAt σ)) :
    ptNorm pts mapR σ fnorm e 0 y = 0 := by sorry
