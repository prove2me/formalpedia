-- Prove2me | Theorems.Thm_CliqueMinors_isMinor_K5_of_card_edgeFinset
-- name    : CliqueMinors.isMinor_K5_of_card_edgeFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:40:37.659975+00:00
-- url     : https://prove2.me/theorems/2473f6c3-2131-4f31-b100-ad8d5c6bc50d
-- title:
--   Clique Minors: is Minor K5 of card edge Finset
-- statement:
--   **Mader (1968).** A finite graph on `n ≥ 3` vertices with at least `3n - 5` edges has a `K₅`
--   minor.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L153-L156
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L153-L156

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]

theorem CliqueMinors.isMinor_K5_of_card_edgeFinset (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) : IsMinor (⊤ : SimpleGraph (Fin 5)) G := by sorry
