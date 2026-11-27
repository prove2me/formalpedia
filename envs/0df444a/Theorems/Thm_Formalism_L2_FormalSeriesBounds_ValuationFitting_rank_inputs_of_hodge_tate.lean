-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_rank_inputs_of_hodge_tate
-- name    : Formalism.L2.FormalSeriesBounds.ValuationFitting.rank_inputs_of_hodge_tate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:43.41798+00:00
-- url     : https://prove2.me/theorems/375867b5-1b10-40d6-a7ec-b68ef901c51f
-- title:
--   Valuation Fitting: rank inputs of hodge tate
-- statement:
--   The Valuation Fitting construction uses the rank inputs of hodge tate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L305-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L305-L382

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

theorem Formalism.L2.FormalSeriesBounds.ValuationFitting.rank_inputs_of_hodge_tate [IsAlgClosed C] [CharZero C] {V : VF C} {d : ℕ}
    {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (big : Fin 2 → ZMod d → Prop) (rh r : ℕ) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (l_odd : V.l ≠ 2)
    (hr : ∀ g a, big g a → pT G (1 - g) a + pT G g a = r)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (hS : HodgeTateSetting V.l vm R O σ cp)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H)
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U) :
    ∃ l1 l2 : Fin 2 → ZMod d → ℝ,
      (∀ g a, big g a → S4.CorDET V.l (pT G g) (l1 g) (l2 g) a) ∧
      (∀ g a, big g a → S4.ThmAi V.l r rh (pT G g) (l2 g) a) ∧
      (∀ g a, big g a → S4.ThmAiii V.v (Matrix.of fun c i => ht g i (T.e g a c)) (l1 g a)) := by sorry
