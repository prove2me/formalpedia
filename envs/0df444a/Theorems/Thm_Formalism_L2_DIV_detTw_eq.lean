-- Prove2me | Theorems.Thm_Formalism_L2_DIV_detTw_eq
-- name    : Formalism.L2.DIV.detTw_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:54.450024+00:00
-- url     : https://prove2.me/theorems/9e78d7aa-9e9f-4175-b3da-871add267c39
-- title:
--   DIV: det Tw eq
-- statement:
--   The DIV construction uses the det Tw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L470-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L470-L475

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

theorem Formalism.L2.DIV.detTw_eq {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) :
    detTwK lam g = ∏ τ, ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ (lam τ).detShift := by sorry
