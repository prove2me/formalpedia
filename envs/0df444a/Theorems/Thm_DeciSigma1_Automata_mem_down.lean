-- Prove2me | Theorems.Thm_DeciSigma1_Automata_mem_down
-- name    : DeciSigma1.Automata.mem_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:37.164806+00:00
-- url     : https://prove2.me/theorems/1d25a15e-2d69-463b-9d45-eeecfd7665bc
-- title:
--   Automata: mem down
-- statement:
--   The Automata construction uses the mem down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L188-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L188-L189

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

theorem DeciSigma1.Automata.mem_down {Γ : List (LitT n V)} {x y : V} :
    x ∈ down Γ y ↔ (x, y) ∈ derivedPairs Γ := by sorry
