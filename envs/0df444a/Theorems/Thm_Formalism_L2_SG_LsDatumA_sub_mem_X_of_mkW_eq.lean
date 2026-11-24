-- Prove2me | Theorems.Thm_Formalism_L2_SG_LsDatumA_sub_mem_X_of_mkW_eq
-- name    : Formalism.L2.SG.LsDatumA.sub_mem_X_of_mkW_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:49.395838+00:00
-- url     : https://prove2.me/theorems/5954fbe6-0f19-43cd-aa04-e8a69d98b139
-- title:
--   Ls Datum A: sub mem X of mk W eq
-- statement:
--   The Ls Datum A construction uses the sub mem X of mk W eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LsDatumA.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LsDatumA.lean#L32-L35

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LsDatumA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.LsDatumA
open Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem Formalism.L2.SG.LsDatumA.sub_mem_X_of_mkW_eq {r : ℕ} {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))}
    (h : H.mkW f x = H.mkW f y) : (x : V) - y ∈ H.X f := by sorry
