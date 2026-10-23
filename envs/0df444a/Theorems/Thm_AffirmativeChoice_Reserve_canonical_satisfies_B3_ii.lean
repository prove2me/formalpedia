-- Prove2me | Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B3_ii
-- name    : AffirmativeChoice.Reserve.canonical_satisfies_B3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:01.370181+00:00
-- url     : https://prove2.me/theorems/264df29a-7bc1-47fd-867b-4f60190676ae
-- title:
--   Proof of Theorem 1, Satisfies B3-ii, pp. 21–22 — worsening a majority among the R lowest-ranked top-tier majorities leaves the reserve unchanged
-- statement:
--   Let $q\ge3$ and let $C$ be a substitutable affirmative action rule satisfying MPI and MTC, with $R_C$ the reserve function of the proof of Theorem 1. Then $R_C$ satisfies Condition B3 (ii): for each problem $(S,\tau,\succ')$ and each majority student $M$ in its top tier, if $\succ$ is an improvement over $\succ'$ for $M$ and fewer than $R_C(S,\tau,\succ)$ top-tier majority students have lower priority than $M$ at $\succ$ (that is, $M$ is one of the $R_C(S,\tau,\succ)$ lowest-ranked top-tier majority students), then
--
--   $$R_C(S,\tau,\succ')=R_C(S,\tau,\succ).$$
--
--   **Formalization Note.** The condition on $M$ is the one of footnote 15, p. 10. $M$ is a top-tier majority at $\succ'$, before the improvement.
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), pp. 21–22, proof of Theorem 1, Satisfies B3-ii; Condition B3 (ii) and footnote 15, p. 10

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

namespace AffirmativeChoice.Reserve

/-- Proof of Theorem 1, "Satisfies B3-ii", pp. 20–22: for a substitutable affirmative action rule
satisfying MPI and MTC, the reserve function of the proof satisfies Condition B3 (ii). -/
theorem canonical_satisfies_B3_ii {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hMPI : MPI C) (hMTC : MTC C) :
    CondB3ii q (canonicalReserve C) := by sorry

end AffirmativeChoice.Reserve
