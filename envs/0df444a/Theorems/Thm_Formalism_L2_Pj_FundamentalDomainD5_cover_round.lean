-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_cover_round
-- name    : Formalism.L2.Pj.FundamentalDomainD5.cover_round
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:49.402146+00:00
-- url     : https://prove2.me/theorems/e89a5381-c654-4df4-8844-996637c22a5e
-- title:
--   Fundamental Domain D5: cover round
-- statement:
--   The Fundamental Domain D5 construction uses the cover round property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DotSelfEqSqNorm.lean#L16-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DotSelfEqSqNorm.lean#L16-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DotSelfEqSqNorm
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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open Matrix

theorem Formalism.L2.Pj.FundamentalDomainD5.cover_round {N : ℕ} (b : Fin N → Fin N → ℝ) (hb : LinearIndependent ℝ b) (ℓ : ℝ)
    (hℓ : ∀ j, b j ⬝ᵥ b j ≤ ℓ ^ 2) (w : Fin N → ℝ) :
    ∃ n : Fin N → ℤ, (w - ∑ j, (n j : ℝ) • b j) ⬝ᵥ (w - ∑ j, (n j : ℝ) • b j) ≤ ((N : ℝ) * ℓ / 2) ^ 2 := by sorry
