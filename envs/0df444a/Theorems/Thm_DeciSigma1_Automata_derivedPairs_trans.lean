-- Prove2me | Theorems.Thm_DeciSigma1_Automata_derivedPairs_trans
-- name    : DeciSigma1.Automata.derivedPairs_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:57.778912+00:00
-- url     : https://prove2.me/theorems/36bcdafc-3fe5-408e-8fb5-a6a440bfb53c
-- title:
--   Automata: derived Pairs trans
-- statement:
--   The Automata construction uses the derived Pairs trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L153-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L153-L156

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Automata.derivedPairs_trans {Γ : List (LitT n V)} {x y z : V}
    (h : (x, y) ∈ derivedPairs Γ) (h' : (y, z) ∈ derivedPairs Γ) : (x, z) ∈ derivedPairs Γ := by sorry
