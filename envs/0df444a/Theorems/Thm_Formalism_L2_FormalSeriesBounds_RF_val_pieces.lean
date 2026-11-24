-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_val_pieces
-- name    : Formalism.L2.FormalSeriesBounds.RF.val_pieces
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:03.733219+00:00
-- url     : https://prove2.me/theorems/402e1f81-1314-48ba-aa82-7dad503c64ee
-- title:
--   RF: val pieces
-- statement:
--   The RF construction uses the val pieces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L85-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L85-L121

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
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
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)
variable {X n}

theorem Formalism.L2.FormalSeriesBounds.RF.val_pieces {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (K : Orb → ℕ) (what₂ : ∀ o, Fin (K o) → ℕ) (pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n)
    (hpl : Function.Injective pl)
    (Pc : ∀ o i, MvPolynomial (Fin (what₂ o i) × WV (I o)) C) (kind : ∀ o i, Fin (what₂ o i) → Knd d)
    (c : ∀ o, Fin (K o) → ℝ)
    (hrow : ∀ o i, RowsOK (X o).G (X o).Alt (Pc o i) (kind o i))
    (hatt : ∀ o i, ∃ (S : ∀ g, Sys ((X o).G g)) (t : ∀ g, I o g → MvPowerSeries (I o g) C),
      (∀ g, (S g).IsT (t g)) ∧ ∃ gr : Fin (what₂ o i) → MvPowerSeries (WV (I o)) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf (X o).hL (Pc o i) (kind o i) gr) ≤ ((c o i : ℝ) : WithTop ℝ))
    (hmem : (fun o => prodAll (plAt n pl o) (Pc o)) ∈ FFimg) :
    ν ≤ ∑ o, ∑ i, c o i := by sorry
