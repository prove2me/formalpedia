-- Prove2me | Theorems.Thm_Formalism_L2_DIV_pderiv_blockAct
-- name    : Formalism.L2.DIV.pderiv_blockAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.40568+00:00
-- url     : https://prove2.me/theorems/92040d82-e999-4d4e-a897-9e5ac252ebd0
-- title:
--   DIV: pderiv block Act
-- statement:
--   The DIV construction uses the pderiv block Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L388-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L388-L440

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
variable {K : Type} [Field K] [StarRing K]
variable {ι : Type} [Fintype ι] {n : ℕ}
omit [StarRing K]

theorem Formalism.L2.DIV.pderiv_blockAct [DecidableEq ι] (V : ι → Matrix (Fin n) (Fin n) K) (s : ι) (a t : Fin n) (g : Pol K ι n) :
    pderiv (s, (a, t)) (Formalism.GradedWeylDivisibility.blockAct K V g) =
      ∑ b : Fin n, C (V s b a) * Formalism.GradedWeylDivisibility.blockAct K V (pderiv (s, (b, t)) g) := by sorry
