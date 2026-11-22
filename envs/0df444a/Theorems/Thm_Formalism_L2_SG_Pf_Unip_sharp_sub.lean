-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_sub
-- name    : Formalism.L2.SG.Pf.Unip.sharp_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:49:11.786174+00:00
-- url     : https://prove2.me/theorems/44256e39-6920-4314-b1ec-5dc0a462c2fe
-- title:
--   Unip: sharp sub
-- statement:
--   The Unip construction uses the sharp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L115-L116

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
variable {J J' : Matrix ι ι K}

theorem Formalism.L2.SG.Pf.Unip.sharp_sub (M N : Matrix ι ι K) : sharp J J' (M - N) = sharp J J' M - sharp J J' N := by sorry
