-- Prove2me | Theorems.Thm_FamousTheorems_affine_communication_lemma_7a
-- name    : FamousTheorems.affine_communication_lemma_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:27.59304+00:00
-- url     : https://prove2.me/theorems/17cc3c3f-f5e2-400f-b354-b90d8d4ac7c0
-- title:
--   The affine communication lemma
-- statement:
--   **The affine communication lemma.** Let $X$ be a scheme and $P$ a property of affine open subschemes of $X$. Suppose that:
--   1. if $P(U)$ and $f\in\mathcal O_X(U)$, then $P(D(f))$ for the basic open $D(f)\subseteq U$;
--   2. if $f_1,\dots,f_n\in\mathcal O_X(U)$ generate the unit ideal and $P(D(f_i))$ for all $i$, then $P(U)$.
--
--   If $P$ holds for the members of some cover of $X$ by affine opens, then $P$ holds for every affine open of $X$.
--
--   This lemma, named by Vakil, is the standard way to show that properties of rings, such as being Noetherian or reduced, define properties of schemes that can be checked on any affine cover. The proof covers the intersection of two affine opens by opens that are basic in both.
--
--   **Formalization note.** Mathlib's `AlgebraicGeometry.of_affine_open_cover`. `X.affineOpens` is the set of affine opens of $X$, and `X.affineBasicOpen f` is the basic open $D(f)$ of $f\in\mathcal O_X(U)$, as an affine open. The cover is given by an indexed family $U_i$ with $\bigcup U_i=X$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AlgebraicGeometry.of_affine_open_cover`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open Opposite

theorem affine_communication_lemma_7a {X : AlgebraicGeometry.Scheme} {P : X.affineOpens → Prop} {ι : Sort*} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i : X.Opens) = ⊤) (V : X.affineOpens)
    (hbasic : ∀ (U : X.affineOpens) (f : X.presheaf.obj (op U)), P U → P (X.affineBasicOpen f))
    (hglue : ∀ (U : X.affineOpens) (s : Finset (X.presheaf.obj (op U))),
      Ideal.span (s : Set (X.presheaf.obj (op U))) = ⊤ → (∀ f : s, P (X.affineBasicOpen f.1)) → P U)
    (hP : ∀ i, P (U i)) : P V := by sorry

end FamousTheorems
