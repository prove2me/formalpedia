-- Prove2me | Theorems.Thm_ChvatalPosa_chvatal
-- name    : ChvatalPosa.chvatal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:18:19.681884+00:00
-- url     : https://prove2.me/theorems/3bcda888-c71e-4429-94e6-a410fb14dcaa
-- title:
--   Chvatal Posa: chvatal
-- statement:
--   **Chvátal's theorem (1972), counting form.** A graph on `n ≥ 3` vertices is Hamiltonian if,
--   for every `i` with `1 ≤ i` and `2 i < n`, whenever at least `i` vertices have degree at most `i`,
--   at least `i + 1` vertices have degree at least `n - i`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L142-L170
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L142-L170

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

theorem ChvatalPosa.chvatal (hn : 3 ≤ Fintype.card V)
    (h : ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
      i ≤ #{v | G.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ G.degree v}) :
    G.IsHamiltonian := by sorry
