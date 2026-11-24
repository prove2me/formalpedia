-- Prove2me | Theorems.Thm_Formalism_L2_DIV_pairK_apply
-- name    : Formalism.L2.DIV.pairK_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:53.393965+00:00
-- url     : https://prove2.me/theorems/a32908aa-a35b-4ec3-97e9-957817b6c9a5
-- title:
--   DIV: pair K apply
-- statement:
--   The DIV construction uses the pair K apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L502-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L502-L504

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

theorem Formalism.L2.DIV.pairK_apply {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) : pairK lam G x y = pairP lam G x.1 y.1 := by sorry
