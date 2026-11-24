-- Prove2me | Theorems.Thm_Formalism_L2_DIV_pairP_vecP
-- name    : Formalism.L2.DIV.pairP_vecP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:09.839281+00:00
-- url     : https://prove2.me/theorems/a5f0350a-28e3-438b-a33d-6604d7ad1857
-- title:
--   DIV: pair P vec P
-- statement:
--   The DIV construction uses the pair P vec P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L702-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L702-L714

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
variable {K : Type} [Field K]
variable [StarRing K]

theorem Formalism.L2.DIV.pairP_vecP (G : Unit → Matrix (Fin 2) (Fin 2) K) (v w : Fin 2 → K) :
    pairP (fun _ => lamVec) G (vecP v) (vecP w) = star v ⬝ᵥ (G () *ᵥ w) := by sorry
