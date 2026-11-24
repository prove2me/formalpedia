-- Prove2me | Theorems.Thm_Formalism_L2_DIV_gLat_injective
-- name    : Formalism.L2.DIV.gLat_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:46.20499+00:00
-- url     : https://prove2.me/theorems/e8fc7433-0823-41ea-9ce0-2b608582d3d3
-- title:
--   DIV: g Lat injective
-- statement:
--   The DIV construction uses the g Lat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L581-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L581-L586

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

theorem Formalism.L2.DIV.gLat_injective (g : GL (Fin n) K) : Function.Injective (gLat (K := K) g) := by sorry
