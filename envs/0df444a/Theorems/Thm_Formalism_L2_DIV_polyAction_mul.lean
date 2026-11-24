-- Prove2me | Theorems.Thm_Formalism_L2_DIV_polyAction_mul
-- name    : Formalism.L2.DIV.polyAction_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:40.983084+00:00
-- url     : https://prove2.me/theorems/774b6a1b-0eaa-4d6e-8bf4-25bc8d017b26
-- title:
--   DIV: poly Action mul
-- statement:
--   The DIV construction uses the poly Action mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L595-L597
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L595-L597

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
omit [NumberField K]

theorem Formalism.L2.DIV.polyAction_mul (lam : ι → DomWeight n) (g h : ι → GL (Fin n) K) (F : Pol K ι n) :
    actP lam (g * h) F = actP lam g (actP lam h F) := by sorry
