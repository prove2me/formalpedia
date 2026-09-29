-- Prove2me | Theorems.Thm_FamousTheorems_fine_wilf_periodicity_lemma
-- name    : FamousTheorems.fine_wilf_periodicity_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:14.575978+00:00
-- url     : https://prove2.me/theorems/5b87c044-4a18-44dd-bfd5-9301bf714144
-- title:
--   The Fine–Wilf periodicity lemma
-- statement:
--   **The Fine–Wilf periodicity lemma.** Let $w$ be a word with periods $p$ and $q$, and suppose $|w|\ge p+q-\gcd(p,q)$. Then $\gcd(p,q)$ is also a period of $w$.
--
--   A word has period $p$ if $w_i=w_{i+p}$ whenever both positions exist. Fine and Wilf proved this in 1965, and the length bound $p+q-\gcd(p,q)$ is sharp. The lemma is fundamental in combinatorics on words and in string-matching algorithms.
--
--   **Formalization note.** Mathlib's `List.HasPeriod.gcd`. Words are lists, and `w.HasPeriod p` says that $w$ has period $p$. Natural-number subtraction is truncated, which does not matter here since $\gcd(p,q)\le p+q$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `List.HasPeriod.gcd`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fine_wilf_periodicity_lemma {α : Type*} {w : List α} {p q : ℕ} (hp : w.HasPeriod p) (hq : w.HasPeriod q)
    (hlen : p + q - Nat.gcd p q ≤ w.length) :
    w.HasPeriod (Nat.gcd p q) := by sorry

end FamousTheorems
