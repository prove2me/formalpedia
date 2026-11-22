-- Prove2me | Theorems.Thm_DeciSigma1_Automata_lowerRun_target
-- name    : DeciSigma1.Automata.lowerRun_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:01.376081+00:00
-- url     : https://prove2.me/theorems/a89a1757-4edf-4e89-9b20-0d17b08950ba
-- title:
--   Automata: lower Run target
-- statement:
--   If `y ≤ z` is derived, the lower run of `y` is contained in that of `z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L272-L279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L272-L279

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

theorem DeciSigma1.Automata.lowerRun_target {Γ : List (LitT n V)} {y z a : V} {w : List (Fin n)}
    (hyz : (y, z) ∈ derivedPairs Γ) (h : a ∈ lowerRun Γ y w) : a ∈ lowerRun Γ z w := by sorry
