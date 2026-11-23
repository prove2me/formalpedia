-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_triv_ok
-- name    : Formalism.L2.Col.GSD.triv_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:49.12818+00:00
-- url     : https://prove2.me/theorems/8b72545b-6d0a-457a-bd60-11bffaeeebc2
-- title:
--   GSD: triv ok
-- statement:
--   The GSD construction uses the triv ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L488-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L488-L502

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (K) (G D : Type) [Group G] [MulAction G D]

theorem Formalism.L2.Col.GSD.triv_ok (h1 : Finite (MulAction.orbitRel.Quotient G D)) (h2 : ∀ d : D, Finite (MulAction.stabilizer G d)) :
    (triv K G D).Ok := by sorry
