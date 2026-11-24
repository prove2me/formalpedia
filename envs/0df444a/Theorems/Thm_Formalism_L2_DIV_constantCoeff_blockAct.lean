-- Prove2me | Theorems.Thm_Formalism_L2_DIV_constantCoeff_blockAct
-- name    : Formalism.L2.DIV.constantCoeff_blockAct
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:32.29365+00:00
-- url     : https://prove2.me/theorems/60f92033-d234-4b57-bd51-286936146b6d
-- title:
--   DIV: constant Coeff block Act
-- statement:
--   The DIV construction uses the constant Coeff block Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L378-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L378-L384

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

theorem Formalism.L2.DIV.constantCoeff_blockAct (U : ι → Matrix (Fin n) (Fin n) K) (g : Pol K ι n) :
    constantCoeff (Formalism.GradedWeylDivisibility.blockAct K U g) = constantCoeff g := by sorry
