-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_2_4_component_additivity
-- name    : C6BipartiteDomination.lemma_2_4_component_additivity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:40:41.266816+00:00
-- url     : https://prove2.me/theorems/87c040c0-2659-59a2-9872-618e6205a3b1
-- title:
--   C6 Bipartite Domination: lemma 2 4 component additivity
-- statement:
--   The C6 Bipartite Domination construction uses the lemma 2 4 component additivity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L291-L312
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L291-L312

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_2_4_component_additivity
    {A B D : Finset V}
    (hparts : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B)
    (hcross : ∀ ⦃a b⦄, a ∈ A → b ∈ B → ¬ G.Adj a b)
    (hD : MinimumBipartiteDominatingSet G D) :
    MinimumBipartiteDominatingOn G A (D ∩ A) ∧
      MinimumBipartiteDominatingOn G B (D ∩ B) ∧
      D.card = (D ∩ A).card + (D ∩ B).card := by sorry
