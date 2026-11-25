-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_aeval_mem_intPoly
-- name    : Formalism.L2.Pj.LocAlg.aeval_mem_intPoly
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:09.318625+00:00
-- url     : https://prove2.me/theorems/17cf46b9-8ea0-4eaf-b2a7-5a5b6f92eff0
-- title:
--   Loc Alg: aeval mem int Poly
-- statement:
--   The Loc Alg construction uses the aeval mem int Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L140-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L140-L149

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

theorem Formalism.L2.Pj.LocAlg.aeval_mem_intPoly {σ τ : Type} {W : Subring Ω} {q : σ → MvPolynomial τ Ω}
    (hq : ∀ s, q s ∈ intPoly τ W) {P : MvPolynomial σ Ω} (hP : P ∈ intPoly σ W) :
    aeval q P ∈ intPoly τ W := by sorry
