-- Prove2me | Theorems.Thm_Formalism_L2_Pj_linIndep_cpts
-- name    : Formalism.L2.Pj.linIndep_cpts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:56.159501+00:00
-- url     : https://prove2.me/theorems/a6f520fd-f76c-4b22-a432-b29639b09bb6
-- title:
--   Pj: lin Indep cpts
-- statement:
--   The Pj construction uses the lin Indep cpts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L108-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean#L108-L134

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

theorem Formalism.L2.Pj.linIndep_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (w : Fin m → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ i, w i * cvalR σ (ψ (a i)) = 0) : w = 0 := by sorry
