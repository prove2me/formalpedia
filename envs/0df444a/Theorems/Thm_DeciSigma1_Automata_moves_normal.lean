-- Prove2me | Theorems.Thm_DeciSigma1_Automata_moves_normal
-- name    : DeciSigma1.Automata.moves_normal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:58.660082+00:00
-- url     : https://prove2.me/theorems/3076af23-e2a1-4425-a878-3a182f524738
-- title:
--   Automata: moves normal
-- statement:
--   Every move derivation has a lowest-point decomposition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L335-L340
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L335-L340

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

theorem DeciSigma1.Automata.moves_normal {Γ : List (LitT n V)} {a b : Config n V} (h : Moves Γ a b) :
    Normal Γ a.1 a.2 b.1 b.2 := by sorry
