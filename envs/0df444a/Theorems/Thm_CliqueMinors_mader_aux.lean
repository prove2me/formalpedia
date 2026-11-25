-- Prove2me | Theorems.Thm_CliqueMinors_mader_aux
-- name    : CliqueMinors.mader_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:02.34706+00:00
-- url     : https://prove2.me/theorems/1614cbfb-c4ab-5e81-90f5-d89e3f4e1709
-- title:
--   Clique Minors: mader aux
-- statement:
--   The Clique Minors construction uses the mader aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L236-L293
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L236-L293

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]

theorem CliqueMinors.mader_aux (r : ℕ) : ∀ (G : SimpleGraph V) (S : Finset V), S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → 2 ^ r * S.card ≤ 8 * G.edgeFinset.card →
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by sorry
