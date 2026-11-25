-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_qj_mem
-- name    : Formalism.L2.Pj.LocAlg.qj_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:15.311728+00:00
-- url     : https://prove2.me/theorems/25dae062-fcd0-406e-8077-79b1ff390e88
-- title:
--   Loc Alg: qj mem
-- statement:
--   The Loc Alg construction uses the qj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L151-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L151-L163

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}

theorem Formalism.L2.Pj.LocAlg.qj_mem {W : Subring Ω} (hyW : ∀ j, yv jc x j / yv jc x j0 ∈ W) (p : TVar D N) :
    qj jc j0 x p ∈ intPoly (SVar D N) W := by sorry
