-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_theta_dot_self
-- name    : Formalism.L2.Pj.FundamentalDomainD5.theta_dot_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:42.969192+00:00
-- url     : https://prove2.me/theorems/1973c8cc-1f46-4321-9efa-500fa338b813
-- title:
--   Fundamental Domain D5: theta dot self
-- statement:
--   The Fundamental Domain D5 construction uses the theta dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ThetaDotSelf.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ThetaDotSelf.lean#L37-L43

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ThetaDotSelf
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
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}

theorem Formalism.L2.Pj.FundamentalDomainD5.theta_dot_self (p : ℕ) {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (w : ι → Fin r → ℂ) :
    rho eqv (Theta p w) ⬝ᵥ rho eqv (Theta p w) = rho eqv w ⬝ᵥ rho eqv w := by sorry
