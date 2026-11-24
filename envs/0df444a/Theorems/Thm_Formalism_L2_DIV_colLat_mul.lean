-- Prove2me | Theorems.Thm_Formalism_L2_DIV_colLat_mul
-- name    : Formalism.L2.DIV.colLat_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:41.243181+00:00
-- url     : https://prove2.me/theorems/91e4c1d5-6fcb-491a-bb27-7a948414ba89
-- title:
--   DIV: col Lat mul
-- statement:
--   The DIV construction uses the col Lat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L556-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L556-L559

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

theorem Formalism.L2.DIV.colLat_mul (g B : GL (Fin n) K) : colLat (g * B) = gLat g (colLat B) := by sorry
