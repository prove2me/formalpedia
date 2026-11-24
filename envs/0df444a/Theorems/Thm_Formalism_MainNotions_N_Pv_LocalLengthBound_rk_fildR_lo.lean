-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_fildR_lo
-- name    : Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:46:09.03319+00:00
-- url     : https://prove2.me/theorems/5594a35d-bcef-44fb-8286-2df08e600a0c
-- title:
--   Local Length Bound: rk fild R lo
-- statement:
--   The Local Length Bound construction uses the rk fild R lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientImageDivisibility/RkMultVOfNotJump.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientImageDivisibility/RkMultVOfNotJump.lean#L96-L99

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
variable (ρ : Representation LL G V)

theorem Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ lo : ℤ, ∀ a ≤ lo, FildR PD ρ τ a = DdRE PD ρ τ := by sorry
