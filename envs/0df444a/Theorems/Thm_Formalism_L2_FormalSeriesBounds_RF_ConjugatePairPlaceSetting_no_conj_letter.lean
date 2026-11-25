-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_no_conj_letter
-- name    : Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.no_conj_letter
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:18.575064+00:00
-- url     : https://prove2.me/theorems/53188cc3-deed-4007-929c-e4d826b5cba3
-- title:
--   Conjugate Pair Place Setting: no conj letter
-- statement:
--   The Conjugate Pair Place Setting construction uses the no conj letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L168-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L168-L191

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}

theorem Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.no_conj_letter (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (τ : T) (a1 : Fin (r τ)) (a2 : Fin (r (cc τ)))
    (b : Fin n)
    (h1 : (⟨τ, a1, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars)
    (h2 : (⟨cc τ, a2, b⟩ : Letter T r n) ∈ (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).vars) : False := by sorry
