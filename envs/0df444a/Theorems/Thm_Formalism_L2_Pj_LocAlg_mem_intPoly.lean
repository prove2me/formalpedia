-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_mem_intPoly
-- name    : Formalism.L2.Pj.LocAlg.mem_intPoly
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:15.682808+00:00
-- url     : https://prove2.me/theorems/6899d1b1-fcc9-4a02-a814-6bff121600d2
-- title:
--   Loc Alg: mem int Poly
-- statement:
--   The Loc Alg construction uses the mem int Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L122-L124

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

theorem Formalism.L2.Pj.LocAlg.mem_intPoly {σ : Type} {W : Subring Ω} {P : MvPolynomial σ Ω} :
    P ∈ intPoly σ W ↔ ∀ e, P.coeff e ∈ W := by sorry
