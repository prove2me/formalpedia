-- Prove2me | Theorems.Thm_Formalism_L2_Pj_ptNorm_nonneg
-- name    : Formalism.L2.Pj.ptNorm_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:22.542291+00:00
-- url     : https://prove2.me/theorems/08c73162-c592-44d2-a14c-8f6f639e5041
-- title:
--   Pj: pt Norm nonneg
-- statement:
--   The Pj construction uses the pt Norm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L113-L115

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

theorem Formalism.L2.Pj.ptNorm_nonneg (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) : 0 ≤ ptNorm pts mapR σ fnorm e f y := by sorry
