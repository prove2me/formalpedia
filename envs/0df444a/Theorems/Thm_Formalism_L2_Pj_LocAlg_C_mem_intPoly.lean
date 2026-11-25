-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocAlg_C_mem_intPoly
-- name    : Formalism.L2.Pj.LocAlg.C_mem_intPoly
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:24.8953+00:00
-- url     : https://prove2.me/theorems/0ad57725-e48c-4f06-979c-0ff6431d85ce
-- title:
--   Loc Alg: C mem int Poly
-- statement:
--   The Loc Alg construction uses the C mem int Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean#L126-L131

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

theorem Formalism.L2.Pj.LocAlg.C_mem_intPoly {σ : Type} {W : Subring Ω} {a : Ω} (ha : a ∈ W) : (C a : MvPolynomial σ Ω) ∈ intPoly σ W := by sorry
