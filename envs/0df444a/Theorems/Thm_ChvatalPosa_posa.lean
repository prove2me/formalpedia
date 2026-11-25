-- Prove2me | Theorems.Thm_ChvatalPosa_posa
-- name    : ChvatalPosa.posa
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:18:04.910439+00:00
-- url     : https://prove2.me/theorems/4cc09418-7008-52b9-9cfc-029bec222664
-- title:
--   Chvatal Posa: posa
-- statement:
--   **Pósa's theorem (1962).** A graph on `n ≥ 3` vertices is Hamiltonian if, for every `k` with
--   `1 ≤ k` and `2 k < n - 1`, fewer than `k` vertices have degree at most `k`, and, when `n` is odd,
--   at most `(n - 1) / 2` vertices have degree at most `(n - 1) / 2`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L175-L195
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L175-L195

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ChvatalPosa.posa (hn : 3 ≤ Fintype.card V)
    (h₁ : ∀ k : ℕ, 1 ≤ k → 2 * k < Fintype.card V - 1 → #{v | G.degree v ≤ k} < k)
    (h₂ : Odd (Fintype.card V) →
      #{v | G.degree v ≤ (Fintype.card V - 1) / 2} ≤ (Fintype.card V - 1) / 2) :
    G.IsHamiltonian := by sorry
