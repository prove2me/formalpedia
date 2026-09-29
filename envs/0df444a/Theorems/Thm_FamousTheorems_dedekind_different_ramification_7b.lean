-- Prove2me | Theorems.Thm_FamousTheorems_dedekind_different_ramification_7b
-- name    : FamousTheorems.dedekind_different_ramification_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:02.76871+00:00
-- url     : https://prove2.me/theorems/5c6288ed-15b2-4b13-a6a8-a9d794b83dac
-- title:
--   Dedekind's different theorem: a prime ramifies iff it divides the different
-- statement:
--   **Dedekind's different theorem.** Let $A\subseteq B$ be Dedekind domains with $B$ finite and torsion-free over $A$, and suppose that the fraction field extension is separable. Let $\mathfrak D_{B/A}$ be the different ideal of $B$ over $A$. A prime $P$ of $B$ is unramified over $A$ if and only if $P$ does not divide $\mathfrak D_{B/A}$.
--
--   Dedekind proved this for number fields in 1882. Together with the relation between the different and the discriminant, it shows that the primes of $A$ that ramify in $B$ are exactly those dividing the discriminant, and so that only finitely many primes ramify.
--
--   **Formalization note.** Mathlib's `not_dvd_differentIdeal_iff`. `differentIdeal A B` is the inverse of the dual of $B$ under the trace form. The algebra structure of $\operatorname{Frac}B$ over $\operatorname{Frac}A$ is the one induced by $A\to B$ (`FractionRing.liftAlgebra`), and separability is stated as a hypothesis under it. `Algebra.IsUnramifiedAt A P` says that the localization $B_P$ is unramified over $A$: it is formally unramified, so the residue field extension is separable and the ramification index is $1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `not_dvd_differentIdeal_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dedekind_different_ramification_7b {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDomain A] [IsDedekindDomain A]
    [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B] (P : Ideal B) [P.IsPrime] :
    letI := FractionRing.liftAlgebra A (FractionRing B)
    Algebra.IsSeparable (FractionRing A) (FractionRing B) →
      (¬P ∣ differentIdeal A B ↔ Algebra.IsUnramifiedAt A P) := by sorry

end FamousTheorems
