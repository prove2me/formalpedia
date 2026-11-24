-- Prove2me | Theorems.Thm_Formalism_L2_Pj_descend_cpts
-- name    : Formalism.L2.Pj.descend_cpts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:34.63216+00:00
-- url     : https://prove2.me/theorems/4080129a-5231-4a6c-8a45-93a78e7389ce
-- title:
--   Pj: descend cpts
-- statement:
--   The Pj construction uses the descend cpts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L136-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L136-L168

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

theorem Formalism.L2.Pj.descend_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {r : ℕ} (a : Fin r → p.R) (w : Fin r → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ j, w j * cvalR σ (ψ (a j)) = 0) (θ : Module.Dual K (CAt σ)) :
    ∑ j, θ (toCAt σ (w j)) • a j = 0 := by sorry
