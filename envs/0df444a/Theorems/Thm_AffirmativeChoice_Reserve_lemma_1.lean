-- Prove2me | Theorems.Thm_AffirmativeChoice_Reserve_lemma_1
-- name    : AffirmativeChoice.Reserve.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:47.9985+00:00
-- url     : https://prove2.me/theorems/3b693dcd-ae46-477e-a2e5-088407ac3924
-- title:
--   Lemma 1, p. 20 — in a substitutable affirmative action rule the bottom-tier order does not change the number of chosen minority students
-- statement:
--   Let $q\ge3$ be the capacity and let $C$ be a substitutable affirmative action rule (capacity-filling, neutral, priority-compatible and substitutable). Let $(S,\tau,\succ)$ and $(S,\tau,\succ')$ be two problems with the same students and types whose top tiers coincide: $T(S,\tau,\succ)=T(S,\tau,\succ')$, and $\succ$ and $\succ'$ order the students of this common top tier in the same way. Then the same number of minority students is chosen at both problems:
--
--   $$|C^m(S,\tau,\succ)|=|C^m(S,\tau,\succ')|.$$
--
--   So the priority ordering inside the bottom tier, and the bottom tier's interleaving with the top tier beyond rank $q$, is irrelevant for how many minority students are chosen. This lemma underlies the construction of the reserve function in the proof of Theorem 1.
--
--   **Formalization Note.** The second problem is the first with its priority function replaced by `pri'`, injective on $S$.
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), p. 20, Lemma 1

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

namespace AffirmativeChoice.Reserve

/-- Lemma 1, p. 20: for a substitutable affirmative action rule, two problems `(S, τ, ≻)` and
`(S, τ, ≻')` whose top tiers coincide have the same number of chosen minority students. -/
theorem lemma_1 {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (P : Problem 𝒮) (pri' : 𝒮 → ℕ) (hinj : Set.InjOn pri' ↑P.S)
    (htop : TopCoincide q P (P.withPri pri' hinj)) :
    (Cm C P).card = (Cm C (P.withPri pri' hinj)).card := by sorry

end AffirmativeChoice.Reserve
