-- Prove2me | Theorems.Thm_AffirmativeChoice_Reserve_canonical_reserve_represents
-- name    : AffirmativeChoice.Reserve.canonical_reserve_represents
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:52.849676+00:00
-- url     : https://prove2.me/theorems/f4868479-19ec-414c-807a-7380c7804c1c
-- title:
--   Proof of Theorem 1, p. 20 — the reserve function R of the proof is a reserve function and C admits a reserve representation via R
-- statement:
--   Let $q\ge3$ and let $C$ be a substitutable affirmative action rule. For a problem $(S,\tau,\succ)$ let
--
--   $$R_C(S,\tau,\succ)=\max\bigl\{|C^A(S',\tau',\succ')| : \tau'(r_k(\succ'))=\tau(r_k(\succ))\ \text{for } k=1,\dots,q\bigr\},$$
--
--   the largest number of minority students chosen via affirmative action among problems whose students of ranks $1,\dots,q$ have the same types as those of $(S,\tau,\succ)$ (a missing $k$-th student counting as its own type). Then $R_C$ is a reserve function (it is at most the number of top-tier majority students and depends only on the top-tier type configuration), and $C$ admits a reserve representation via $R_C$: at every problem, $C$ chooses all top-tier minority students, the $R_C$ highest-priority bottom-tier minority students (all of them if fewer), and fills the remaining seats with the highest-priority majority students.
--
--   This is the first step of the paper's proof of Theorem 1 (⇒); it uses neither MPI nor MTC.
--
--   **Formalization Note.** The paper defines $R(\rho)=|C^A(S,\tau,\succ)|$ at one problem with $|S^m|=q$ whose top tier coincides with $\rho$. Here the reserve is the supremum (`sSup` on ℕ) over all problems with the same top-tier type configuration; the set contains $|C^A(S,\tau,\succ)|$ and is bounded by $q$, so the supremum is a maximum. When $|\mathcal S|\ge 2q$ the paper's problem exists and attains it, so the two definitions agree; the supremum form is defined for every universe.
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), p. 20, proof of Theorem 1 (definition of R)

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

namespace AffirmativeChoice.Reserve

/-- Proof of Theorem 1, p. 20: for a substitutable affirmative action rule `C`, the reserve
function `R` of the proof is a reserve function and `C` admits a reserve representation via
`R`. -/
theorem canonical_reserve_represents {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C) :
    IsReserveFunction q (canonicalReserve C) ∧ IsReserveRep C (canonicalReserve C) := by sorry

end AffirmativeChoice.Reserve
