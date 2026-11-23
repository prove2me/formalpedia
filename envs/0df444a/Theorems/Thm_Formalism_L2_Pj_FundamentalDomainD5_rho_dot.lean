-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_dot
-- name    : Formalism.L2.Pj.FundamentalDomainD5.rho_dot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:20.189341+00:00
-- url     : https://prove2.me/theorems/745d7508-fbc2-49a9-ae22-55aaf1b0da0c
-- title:
--   Fundamental Domain D5: rho dot
-- statement:
--   The Fundamental Domain D5 construction uses the rho dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/RhoDotSelf.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/RhoDotSelf.lean#L42-L47

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

theorem Formalism.L2.Pj.FundamentalDomainD5.rho_dot (w w' : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w' = ∑ i, ∑ a, (conj (w i a) * w' i a).re := by sorry
