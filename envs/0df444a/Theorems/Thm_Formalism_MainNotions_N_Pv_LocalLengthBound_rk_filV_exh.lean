-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_filV_exh
-- name    : Formalism.MainNotions.N.Pv.LocalLengthBound.rk_filV_exh
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:03:34.061681+00:00
-- url     : https://prove2.me/theorems/26230d25-0df9-472f-bed9-905329804bd6
-- title:
--   Local Length Bound: rk fil V exh
-- statement:
--   The Local Length Bound construction uses the rk fil V exh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientImageDivisibility/RkMultVOfNotJump.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientImageDivisibility/RkMultVOfNotJump.lean#L34-L44

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientImageDivisibility_RkMultVOfNotJump
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.Pv Formalism.MainNotions.N.Pv.LocalLengthBound
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem Formalism.MainNotions.N.Pv.LocalLengthBound.rk_filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by sorry
