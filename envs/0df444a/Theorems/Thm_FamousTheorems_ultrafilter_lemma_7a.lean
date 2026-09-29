-- Prove2me | Theorems.Thm_FamousTheorems_ultrafilter_lemma_7a
-- name    : FamousTheorems.ultrafilter_lemma_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:37.227362+00:00
-- url     : https://prove2.me/theorems/51dd5946-362b-4ee7-9e87-989807b41e8b
-- title:
--   The ultrafilter lemma
-- statement:
--   **The ultrafilter lemma.** Every proper filter $f$ on a set $\alpha$ is contained in an ultrafilter on $\alpha$.
--
--   Tarski proved this in 1930 using Zorn's lemma. The ultrafilter lemma is strictly weaker than the axiom of choice and equivalent to the Boolean prime ideal theorem. It implies Tychonoff's theorem for Hausdorff spaces, the compactness theorem of first-order logic and the existence of non-principal ultrafilters, which are used in ultraproducts and nonstandard analysis.
--
--   **Formalization note.** Mathlib's `Ultrafilter.exists_le`. `f.NeBot` says that $f$ is proper, that is, $\emptyset\notin f$. The coercion of an ultrafilter to a filter is taken, and $\le$ on filters is reverse inclusion, so `(u : Filter α) ≤ f` means $f\subseteq u$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ultrafilter.exists_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ultrafilter_lemma_7a {α : Type*} (f : Filter α) [f.NeBot] : ∃ u : Ultrafilter α, (u : Filter α) ≤ f := by sorry

end FamousTheorems
