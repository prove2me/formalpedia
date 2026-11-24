-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_coefVia_apply
-- name    : Formalism.L2.Pj.FJ.coefVia_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:20.143725+00:00
-- url     : https://prove2.me/theorems/62e7a8a8-2ce4-4691-b7a2-065ffa315cb4
-- title:
--   FJ: coef Via apply
-- statement:
--   The FJ construction uses the coef Via apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L124-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L124-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Pj
open Formalism.L2.Pj.FJ
variable {K : Type} [Field K]
variable (σ : K →+* ℂ) (Ω : Type)
variable {σ Ω}

theorem Formalism.L2.Pj.FJ.coefVia_apply {N : ℕ} {C : Type} [AddCommGroup C] [Module K C]
    (act : (Fin N → ℝ) → Ω → Ω) (S : Set Ω) (ph : Fin N → ℝ) (rd : C →ₛₗ[σ] (Ω → ℂ))
    (hrd : ∀ F, rd F ∈ OrbInt act S) (F : C) {x : Ω} (hx : x ∈ S) :
    (coefVia act S ph rd hrd F : Ω → ℂ) x = coefFn act ph (rd F) x := by sorry
