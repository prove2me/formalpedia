-- Prove2me | Theorems.Thm_FamousTheorems_five_lemma
-- name    : FamousTheorems.five_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:31.934379+00:00
-- url     : https://prove2.me/theorems/b392a9ce-6711-4688-861b-3126fce3b5bf
-- title:
--   The five lemma
-- statement:
--   **The five lemma.** In an abelian category, let
--   $$\begin{array}{ccccccccc}A_0&\to&A_1&\to&A_2&\to&A_3&\to&A_4\\ \downarrow{\scriptstyle\varphi_0}&&\downarrow{\scriptstyle\varphi_1}&&\downarrow{\scriptstyle\varphi_2}&&\downarrow{\scriptstyle\varphi_3}&&\downarrow{\scriptstyle\varphi_4}\\ B_0&\to&B_1&\to&B_2&\to&B_3&\to&B_4\end{array}$$
--   be a commutative diagram with exact rows. If $\varphi_0$ is an epimorphism, $\varphi_1$ and $\varphi_3$ are isomorphisms, and $\varphi_4$ is a monomorphism, then $\varphi_2$ is an isomorphism.
--
--   This is the sharp form of the five lemma, where the outer maps need only be epi and mono. It is used constantly in algebraic topology and homological algebra to show that a map inducing isomorphisms on neighbouring terms of long exact sequences is itself an isomorphism.
--
--   **Formalization note.** Mathlib's `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`. Rows are `ComposableArrows C 4` (sequences of four composable arrows, five objects), exactness is `.Exact`, and `ComposableArrows.app' φ i` is the $i$-th vertical component of the morphism of rows `φ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem five_lemma {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C] {R₁ R₂ : CategoryTheory.ComposableArrows C 4}
    (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (φ : R₁ ⟶ R₂)
    (h₀ : CategoryTheory.Epi (CategoryTheory.ComposableArrows.app' φ 0))
    (h₁ : CategoryTheory.IsIso (CategoryTheory.ComposableArrows.app' φ 1))
    (h₃ : CategoryTheory.IsIso (CategoryTheory.ComposableArrows.app' φ 3))
    (h₄ : CategoryTheory.Mono (CategoryTheory.ComposableArrows.app' φ 4)) :
    CategoryTheory.IsIso (CategoryTheory.ComposableArrows.app' φ 2) := by sorry

end FamousTheorems
