-- Prove2me | Theorems.Thm_FamousTheorems_kruskal_katona
-- name    : FamousTheorems.kruskal_katona
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:59.69782+00:00
-- url     : https://prove2.me/theorems/51018bac-b142-4b69-abb4-19a189329387
-- title:
--   The Kruskal–Katona theorem
-- statement:
--   **The Kruskal–Katona theorem.** Among all families of $k$ $r$-element subsets of $\{0,\dots,n-1\}$, the initial segment of length $k$ in the colexicographic order has the smallest shadow. The shadow of a family is the set of all $(r-1)$-subsets of its members. Concretely, if $\mathcal A$ is $r$-uniform and $\mathcal C$ is a colex initial segment of $r$-sets with $|\mathcal C|\le|\mathcal A|$, then $|\partial\mathcal C|\le|\partial\mathcal A|$.
--
--   It determines exactly which $f$-vectors occur for simplicial complexes. It is the source of the Lovász version of the shadow bound and a standard route to the Erdős–Ko–Rado theorem.
--
--   **Formalization note.** Mathlib's `Finset.kruskal_katona`; `Finset.shadow` is the shadow and `Finset.Colex.IsInitSeg 𝒞 r` says `𝒞` is an initial segment of the colex order on `r`-sets.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.kruskal_katona`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kruskal_katona {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))} (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r)
    (h𝒞𝒜 : 𝒞.card ≤ 𝒜.card) (h𝒞 : Finset.Colex.IsInitSeg 𝒞 r) :
    (Finset.shadow 𝒞).card ≤ (Finset.shadow 𝒜).card := by sorry

end FamousTheorems
