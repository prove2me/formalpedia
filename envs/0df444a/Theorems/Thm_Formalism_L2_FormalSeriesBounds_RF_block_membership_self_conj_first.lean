-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_block_membership_self_conj_first
-- name    : Formalism.L2.FormalSeriesBounds.RF.block_membership_self_conj_first
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:53:18.858947+00:00
-- url     : https://prove2.me/theorems/a00091cc-c920-43d9-a111-68165f27a737
-- title:
--   RF: block membership self conj first
-- statement:
--   The RF construction uses the block membership self conj first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemC.lean#L99-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemC.lean#L99-L112

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksCChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
  (O : Subring C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

theorem Formalism.L2.FormalSeriesBounds.RF.block_membership_self_conj_first (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree) (h4 : IsotropicToStdSubstIntegral)
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (conj : ∀ o t, cc (tau o t) = tau o (t + 1))
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (gm_int : ∀ o t q s, gm o t q s ∈ O)
    (hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (alt : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s) (tie : WtTieC r tau gaC a) :
    BlockMembershipSelfConjugate X N F (selfConjTuplesInLattice r cc isX a tau gm O plc) gaC := by sorry
