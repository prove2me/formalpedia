-- Prove2me | Theorems.Thm_AlmostKing_Query_lemma_14
-- name    : AlmostKing.Query.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:06.057202+00:00
-- url     : https://prove2.me/theorems/44969d09-b904-45e1-a2cf-9a38e3640cdb
-- title:
--   Lemma 14 — a king in two consecutive tournaments
-- statement:
--   Let $T_1,T_2$ be tournaments on the same nonempty finite vertex set $V$. There exists $v\in V$ such that
--   $$\{v\}\cup N_{T_1}^+(v)\cup N_{T_2}^+(v)\cup N_{T_2}^+(N_{T_1}^+(v))=V.$$
--   Thus every other vertex is reached by an arc in either tournament or by an arc of $T_1$ followed by an arc of $T_2$.
--
--   This is the two-tournament reachability result attributed to Afek, Gafni and Linial, with the order of the two arcs preserved.
--
--   Differences from the source:
--   - generalization: tournaments on $[n]$ for positive $n$ → tournaments on any nonempty finite vertex type; reason: a bijection with $[n]$ preserves arcs and the conclusion
--   - encoding: equality of the displayed union with the whole vertex set → for every vertex, the disjunction of membership in the four displayed sets; reason: these are logically equivalent forms of the same coverage statement
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Lemma 14 ([AGL19, Theorem 1]), p. 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

namespace AlmostKing.Query

/-- Lemma 14, p. 10. The first arc of the two-arc path is in T₁, the second in T₂. -/
theorem lemma_14 {V : Type*} [Fintype V] [Nonempty V]
    (T₁ T₂ : Digraph V) (h₁ : IsTournament T₁) (h₂ : IsTournament T₂) :
    ∃ v : V, ∀ u : V, u = v ∨ T₁.Adj v u ∨ T₂.Adj v u ∨
      ∃ z : V, T₁.Adj v z ∧ T₂.Adj z u := by sorry

end AlmostKing.Query
