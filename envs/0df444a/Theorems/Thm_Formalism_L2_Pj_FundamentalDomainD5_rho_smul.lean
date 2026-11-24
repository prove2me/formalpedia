-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_smul
-- name    : Formalism.L2.Pj.FundamentalDomainD5.rho_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:23.422276+00:00
-- url     : https://prove2.me/theorems/149cc8fb-ae83-47e9-91b8-f0b9ea03a6b2
-- title:
--   Fundamental Domain D5: rho smul
-- statement:
--   The Fundamental Domain D5 construction uses the rho smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/RhoDotSelf.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/RhoDotSelf.lean#L26-L29

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

theorem Formalism.L2.Pj.FundamentalDomainD5.rho_smul (c : ℝ) (w : ι → Fin r → ℂ) : rho eqv ((c : ℂ) • w) = c • rho eqv w := by sorry
