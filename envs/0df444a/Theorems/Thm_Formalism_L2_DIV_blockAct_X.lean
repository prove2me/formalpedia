-- Prove2me | Theorems.Thm_Formalism_L2_DIV_blockAct_X
-- name    : Formalism.L2.DIV.blockAct_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:44.250562+00:00
-- url     : https://prove2.me/theorems/1bc6102a-440d-44be-9e82-b9dcb0bed505
-- title:
--   DIV: block Act X
-- statement:
--   The DIV construction uses the block Act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L373-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L373-L375

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

theorem Formalism.L2.DIV.blockAct_X (U : ι → Matrix (Fin n) (Fin n) K) (v : ι × Fin n × Fin n) :
    Formalism.GradedWeylDivisibility.blockAct K U (X v) = ∑ b : Fin n, C (U v.1 v.2.1 b) * X (v.1, (b, v.2.2)) := by sorry
