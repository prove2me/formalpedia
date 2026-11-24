-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_dot_self
-- name    : Formalism.L2.Pj.FundamentalDomainD5.rho_dot_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:59.887967+00:00
-- url     : https://prove2.me/theorems/d1ef2ee6-c5f4-4a44-b3c6-9af09b766875
-- title:
--   Fundamental Domain D5: rho dot self
-- statement:
--   The Fundamental Domain D5 construction uses the rho dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/RhoDotSelf.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/RhoDotSelf.lean#L49-L53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
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
open Matrix ComplexConjugate
variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)

theorem Formalism.L2.Pj.FundamentalDomainD5.rho_dot_self (w : ι → Fin r → ℂ) : rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ a, ‖w i a‖ ^ 2 := by sorry
