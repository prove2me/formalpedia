-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_frobSum_shift
-- name    : Formalism.L2.FormalSeriesBounds.ValuationFitting.frobSum_shift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:34:43.702254+00:00
-- url     : https://prove2.me/theorems/6bd36519-2e68-4233-8471-e0f2b86e983c
-- title:
--   Valuation Fitting: frob Sum shift
-- statement:
--   The Valuation Fitting construction uses the frob Sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L274-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L274-L303

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.ValuationFitting
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.ValuationFitting.frobSum_shift {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    {G : ∀ g, Cart V d (I g) (J g)} {big : Fin 2 → ZMod d → Prop} {rh : ℕ} {h : Fin 2 → ℕ}
    {ht : ∀ g, Fin (h g) → I g → C}
    {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    {O : Type} [CommRing O] [Algebra ℤ_[V.l] O] {σ : O ≃ₐ[ℤ_[V.l]] O} {cp : R} {gB : ℕ}
    {H : HodgeTateDatum V.l gB vm R O σ cp} {U : UnramData V.l gB vm R O σ cp H}
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U) (g : Fin 2) (a : ZMod d) :
    ReciprocityTheory.PGsh.Up.frobSum U (T.ix g a) =
      S4.frobSum V.l (pT G g) a - (rh : ℝ) / ((V.l : ℝ) - 1) := by sorry
