-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_3_3
-- name    : BourgainUnion.Euclidean.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:44.034462+00:00
-- url     : https://prove2.me/theorems/c8db63d6-39f8-4996-9634-0bf07f97aa11
-- title:
--   Lemma 3.3 — distortion controls extensions
-- statement:
--   Let $X$ be a metric space admitting a normalized embedding into $\ell_2$ with factor $D$, and let $\varnothing\ne V\subseteq X$. Every $L$-Lipschitz map $f:V\to\ell_2$, with $L\ge0$, has an extension $F:X\to\ell_2$ such that
--   $$F|_V=f,\qquad\|F(x)-F(y)\|\le DLd(x,y).$$
--   In particular,
--   $$e_X(V)\le c_2(X).$$
--   The infimum inequality is a separate conclusion; it does not assume an embedding attaining $c_2(X)$. This gives the lower half of the two-sided comparison.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: maps defined only on a specified subset → total representatives on the ambient type, constrained only on that subset; reason: every subset map has a total representative by setting it to zero off the subset; those extra values impose no conditions
--   - encoding: the least distortion or extension factor, potentially infinite → an infimum in ℝ≥0∞ of finite admissible factors at least one; reason: empty admissible sets give infinity; no real infimum default or unjustified attainment is used; empty and singleton spaces have the conventional factor one
--   - encoding: Lip(F)≤D Lip(f) → for every real upper Lipschitz bound L≥0, a DL-Lipschitz extension; reason: this expresses the same extension property without a real supremum over potentially empty point-pair sets; L=0 includes constant maps
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 11, Lemma 3.3

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_ExtensionModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 3.3: every map and its extension, followed by the infimum inequality. -/
theorem lemma_3_3 {X : Type*} [MetricSpace X]
    (D : ℝ) (hD : Embeds (X := X) D) (V : Set X) (hV : V.Nonempty) :
    (∀ L : ℝ, 0 ≤ L → ∀ f : X → H2, LipOn L f V →
      ∃ F : X → H2, Set.EqOn F f V ∧ LipOn (D*L) F Set.univ) ∧
    extensionConstant V ≤ c2 X := by sorry

end BourgainUnion.Euclidean
