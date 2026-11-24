-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cnorm_isom
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.cnorm_isom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:18:02.830024+00:00
-- url     : https://prove2.me/theorems/94a67285-73f6-423f-8233-70ece2c620a2
-- title:
--   RBTie: cnorm isom
-- statement:
--   The RBTie construction uses the cnorm isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieMu.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieMu.lean#L21-L32

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.cnorm_isom {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (W : Matrix m n ℂ)
    (hW : Wᴴ * W = 1) (c : n → ℂ) : Formalism.HermitianLatticesTheory.cnorm (W *ᵥ c) = Formalism.HermitianLatticesTheory.cnorm c := by sorry
