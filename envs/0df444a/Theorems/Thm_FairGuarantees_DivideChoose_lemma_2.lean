-- Prove2me | Theorems.Thm_FairGuarantees_DivideChoose_lemma_2
-- name    : FairGuarantees.DivideChoose.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:30.227131+00:00
-- url     : https://prove2.me/theorems/9f293259-88da-43e5-b8ca-1c6c2362572a
-- title:
--   Lemma 2, p. 14 — a largest properly matchable set of agents exists and contains the agent who likes everything
-- statement:
--   Let $M$ (agents) and $R$ (objects) be finite sets with $|M|=|R|$ and a relation "agent $a$ likes object $r$". Assume every agent of $M$ likes at least one object of $R$ and some agent $i^*\in M$ likes all objects of $R$. Then there is a set $M^*\subseteq M$ with $i^*\in M^*$ that is properly matched to some $R^*\subseteq R$ and is the largest such set:
--   $$\widetilde M\text{ properly matched to }\widetilde R\ \Longrightarrow\ \widetilde M\subseteq M^* .$$
--
--   This makes the matching step of the Divide & Choose rule well defined: the set of agents served at each step is unique.
--
--   **Formalization Note** "Properly matched" is the predicate `IsProperMatch` of the DCRule definition, with an explicit matching map $f$; "outside $\widetilde M$" means in $M\setminus\widetilde M$.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 14, §4, Lemma 2

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_DivideChoose_DCRule

namespace FairGuarantees.DivideChoose

/-- Lemma 2, p. 14: if `|M| = |R|`, every agent of `M` likes some object of `R`, and the agent
`i⋆ ∈ M` likes every object of `R`, then there is a largest set `M⋆` of properly matchable
agents, and it contains `i⋆`: `M⋆` is properly matched to some `R⋆ ⊆ R`, and every `M'`
properly matched to some `R'` satisfies `M' ⊆ M⋆`. -/
theorem lemma_2 {α β : Type*} [DecidableEq α] (M : Finset α) (R : Finset β)
    (likes : α → β → Prop) (hcard : M.card = R.card) (hlike : ∀ a ∈ M, ∃ r ∈ R, likes a r)
    (istar : α) (hi : istar ∈ M) (hall : ∀ r ∈ R, likes istar r) :
    ∃ Mstar : Finset α, Mstar ⊆ M ∧ istar ∈ Mstar ∧
      (∃ (Rstar : Finset β) (f : α → β), IsProperMatch M R likes Mstar Rstar f) ∧
      ∀ (M' : Finset α) (R' : Finset β) (g : α → β), IsProperMatch M R likes M' R' g →
        M' ⊆ Mstar := by sorry

end FairGuarantees.DivideChoose
