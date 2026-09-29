-- Prove2me | Theorems.Thm_FamousTheorems_cyclotomic_five_pid_7b
-- name    : FamousTheorems.cyclotomic_five_pid_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:05.758827+00:00
-- url     : https://prove2.me/theorems/957fdad5-ef11-4603-a422-1e5100f77e49
-- title:
--   The ring of integers of ℚ(ζ₅) is a principal ideal domain (class number one)
-- statement:
--   **The ring of integers of $\mathbb Q(\zeta_5)$ is a principal ideal domain.** Let $K=\mathbb Q(\zeta_5)$ be the fifth cyclotomic field. Then its ring of integers $\mathbb Z[\zeta_5]$ is a principal ideal domain; equivalently, $K$ has class number $1$.
--
--   Kummer's approach to Fermat's Last Theorem works directly in $\mathbb Z[\zeta_p]$ when this ring has unique factorization, which is the case exactly for $p\le19$. For $p=5$ this gives a proof of Fermat's Last Theorem for exponent $5$. The proof uses the Minkowski bound: every ideal class contains an ideal of norm less than $2$, so it is trivial.
--
--   **Formalization note.** Mathlib's `IsCyclotomicExtension.Rat.five_pid`. `NumberField.RingOfIntegers K` is the ring of integers of $K$, and `IsPrincipalIdealRing` says that every ideal is principal.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsCyclotomicExtension.Rat.five_pid`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cyclotomic_five_pid_7b (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) := by sorry

end FamousTheorems
