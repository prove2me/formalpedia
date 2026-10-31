-- Prove2me | Theorems.Thm_AffirmativeChoice_Reserve_theorem_1_forward
-- name    : AffirmativeChoice.Reserve.theorem_1_forward
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:49.298985+00:00
-- url     : https://prove2.me/theorems/45b18ebb-cd47-4218-8fca-0a44f024b284
-- title:
--   Theorem 1 (⇒), p. 10 — a substitutable affirmative action rule satisfying MPI and MTC admits a bounded reserve representation (the (⇐) half is false as printed)
-- statement:
--   Let $\mathcal S$ be a nonempty finite set of students and $q\ge3$ the capacity of a school. Let $C$ be a choice rule that is a substitutable affirmative action rule, that is, it satisfies
--
--   1. capacity-filling, neutrality and priority-compatibility,
--   2. substitutability,
--   3. monotonicity in priority improvements (MPI), and
--   4. monotonicity in type changes (MTC).
--
--   Then $C$ has a bounded reserve representation: there is a reserve function $R$ satisfying Conditions B1, B2 and B3 such that, at every problem $(S,\tau,\succ)$,
--
--   $$C(S,\tau,\succ)=T^m\ \cup\ \{\text{the } R(S,\tau,\succ) \text{ highest-priority students of } B^m\}\ \cup\ \{\text{the highest-priority majority students, filling the remaining seats}\}.$$
--
--   This is the "only if" direction of Theorem 1 of the paper: every rule satisfying the axioms is a reserve rule whose reserve number depends only on the types and ranks of the top-tier students and changes by at most one under a type change or a priority change.
--
--   **Formalization Note.** Only the (⇒) half is stated. The (⇐) half of Theorem 1 is false as printed: with $q=3$, the reserve $R=1$ if the top tier has at most one minority and $R=0$ otherwise satisfies B1–B3, yet for $a\succ b\succ c\succ d\succ e$ with minorities $d,e$ it chooses $\{a,b,d\}$ from $\{a,b,c,d,e\}$ and $\{a,d,e\}$ from $\{a,b,d,e\}$, violating substitutability. No lower bound on $|\mathcal S|$ is assumed, as in the paper's model. The p. 6 typos are read as intended (see the model file).
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), p. 10, Theorem 1 (⇒); proof in Appendix A.1, pp. 20–22

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

namespace AffirmativeChoice.Reserve

/-- Theorem 1 (⇒), p. 10: a substitutable affirmative action rule that satisfies monotonicity in
priority improvements and monotonicity in type changes admits a bounded reserve representation.
(The converse half of Theorem 1 is false as printed and is not stated.) -/
theorem theorem_1_forward {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hMPI : MPI C) (hMTC : MTC C) :
    HasBoundedReserveRep C := by sorry

end AffirmativeChoice.Reserve
