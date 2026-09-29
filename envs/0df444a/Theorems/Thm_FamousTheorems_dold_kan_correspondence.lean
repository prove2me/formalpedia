-- Prove2me | Theorems.Thm_FamousTheorems_dold_kan_correspondence
-- name    : FamousTheorems.dold_kan_correspondence
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:55.972986+00:00
-- url     : https://prove2.me/theorems/e16f934a-27a4-4edf-a88d-c1d738190f18
-- title:
--   The Dold–Kan correspondence
-- statement:
--   **The Dold–Kan correspondence.** Let $\mathcal C$ be a preadditive category that is idempotent complete and has finite coproducts, for example the category of abelian groups or of modules over a ring. Then the category of simplicial objects in $\mathcal C$ is equivalent to the category of chain complexes in $\mathcal C$ concentrated in nonnegative degrees.
--
--   The correspondence is given by the normalised Moore complex, with inverse a Kan construction. It lets homological algebra be carried out with simplicial methods and conversely, and it is fundamental in homotopical algebra and in the construction of Eilenberg–MacLane spaces.
--
--   **Formalization note.** Mathlib's `CategoryTheory.Idempotents.DoldKan.equivalence`, which constructs the equivalence; the statement asserts that an equivalence of categories `SimplicialObject C ≌ ChainComplex C ℕ` exists.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Idempotents.DoldKan.equivalence`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dold_kan_correspondence {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Preadditive C] [CategoryTheory.IsIdempotentComplete C]
    [CategoryTheory.Limits.HasFiniteCoproducts C] :
    Nonempty (CategoryTheory.Equivalence (CategoryTheory.SimplicialObject C) (ChainComplex C ℕ)) := by sorry

end FamousTheorems
