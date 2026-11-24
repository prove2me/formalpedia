-- Prove2me | Theorems.Thm_Formalism_L2_Pj_eq_zero_of_cpts
-- name    : Formalism.L2.Pj.eq_zero_of_cpts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:44.166658+00:00
-- url     : https://prove2.me/theorems/e0a0124a-1199-49bd-a428-f277d33bb280
-- title:
--   Pj: eq zero of cpts
-- statement:
--   The Pj construction uses the eq zero of cpts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L46-L49

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
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

theorem Formalism.L2.Pj.eq_zero_of_cpts (σ : K →+* ℂ) (p : TRing K) (a : p.R) (h : ∀ ψ : p.R →ₐ[K] CAt σ, ψ a = 0) : a = 0 := by sorry
