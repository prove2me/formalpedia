-- Prove2me | Theorems.Thm_FamousTheorems_snake_lemma
-- name    : FamousTheorems.snake_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:40.248671+00:00
-- url     : https://prove2.me/theorems/76e0d44b-6ea8-40a6-8554-e9073eb7a527
-- title:
--   The snake lemma
-- statement:
--   **The snake lemma.** In an abelian category, consider a commutative diagram with exact rows
--   $$\begin{array}{ccccccc} & A_1&\to&B_1&\to&C_1&\to 0\\ &\downarrow{\scriptstyle a}&&\downarrow{\scriptstyle b}&&\downarrow{\scriptstyle c}\\ 0\to&A_2&\to&B_2&\to&C_2& \end{array}$$
--   Then there is a connecting morphism $\delta:\ker c\to\operatorname{coker}a$ making the six-term sequence
--   $$\ker a\to\ker b\to\ker c\xrightarrow{\ \delta\ }\operatorname{coker}a\to\operatorname{coker}b\to\operatorname{coker}c$$
--   exact.
--
--   The snake lemma is the basic tool of homological algebra. It produces the long exact sequence in homology from a short exact sequence of chain complexes, and it is behind many dimension and index computations.
--
--   **Formalization note.** Mathlib's `CategoryTheory.ShortComplex.SnakeInput.snake_lemma`. A `ShortComplex.SnakeInput C` bundles the diagram together with the kernel and cokernel rows. `S.composableArrows` is the six-term sequence above, including the connecting morphism $\delta$, and `.Exact` asserts exactness at every position.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.ShortComplex.SnakeInput.snake_lemma`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem snake_lemma {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C] (S : CategoryTheory.ShortComplex.SnakeInput C) :
    S.composableArrows.Exact := by sorry

end FamousTheorems
