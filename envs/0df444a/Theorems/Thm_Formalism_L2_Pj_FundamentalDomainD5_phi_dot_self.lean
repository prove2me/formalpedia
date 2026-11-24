-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_phi_dot_self
-- name    : Formalism.L2.Pj.FundamentalDomainD5.phi_dot_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:17.561717+00:00
-- url     : https://prove2.me/theorems/fdbbcfed-687e-4b60-b510-886f6807a006
-- title:
--   Fundamental Domain D5: phi dot self
-- statement:
--   The Fundamental Domain D5 construction uses the phi dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ThetaDotSelf.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ThetaDotSelf.lean#L45-L51

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

theorem Formalism.L2.Pj.FundamentalDomainD5.phi_dot_self (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) {N : ℕ}
    (eqv : Fin N ≃ ι × Fin r × Fin 2) (v : Fin r → K) :
    rho eqv (Phi σ Q v) ⬝ᵥ rho eqv (Phi σ Q v) = majSq σ Q v := by sorry
