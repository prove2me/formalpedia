-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_CH_of_HTD
-- name    : Formalism.L2.FormalSeriesBounds.ValuationFitting.CH_of_HTD
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T18:35:22.875356+00:00
-- url     : https://prove2.me/theorems/f51a9e34-d5cb-42bb-9713-504f0253f3d9
-- title:
--   Valuation Fitting: CH of HTD
-- statement:
--   The Valuation Fitting construction uses the CH of HTD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L213-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L213-L232

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

theorem Formalism.L2.FormalSeriesBounds.ValuationFitting.CH_of_HTD [IsAlgClosed C] [CharZero C] {V : VF C} {d : ℕ} [NeZero d]
    {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (G : ∀ g, Cart V d (I g) (J g)) (n j j' rh r : ℕ) (r_eq : r = n + j + j')
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (rk_big : ∀ g a, big g a → pT G g a = n + j)
    (rk_small : ∀ g a, ¬ big g a → pT G g a = j')
    (l_odd : V.l ≠ 2) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (hS : HodgeTateSetting V.l vm R O σ cp)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H)
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U)
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by sorry
