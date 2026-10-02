-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexity_convex_extensible_iff_argmin_hole_free
-- name    : DiscreteConvex.IntegralConvexity.convex_extensible_iff_argmin_hole_free
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:51:16.775816+00:00
-- url     : https://prove2.me/theorems/6eac6065-09d7-4c37-8308-7ed315b0c526
-- title:
--   Proposition 3.18 -- convex extensibility and hole-free perturbed minimizers
-- statement:
--   **Proposition 3.18** (p.93). If $f$ is convex extensible, then $\arg\min f[-p]$ is hole free for every $p \in \mathbb R^n$. The converse also holds if $\operatorname{dom}_{\mathbb Z} f$ is bounded.
--
--   **Formalization Note.** Boundedness of $\operatorname{dom}_{\mathbb Z} f$ is represented as the existence of a single real bound $R$ on every coordinate of every point of the domain, the natural reading of "bounded" for a subset of $\mathbb Z^n$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Proposition 3.18.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Proposition 3.18

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_ConvexExtensible
import Definitions.Def_DiscreteConvex_IntegralConvexity_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexity_HoleFree

namespace DiscreteConvex.IntegralConvexity

/-- Proposition 3.18 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.93). If `f` is convex
extensible, then `arg min f[-p]` is hole free for every `p ∈ Rⁿ`. The converse also holds if
`dom_Z f` is bounded (represented here as a common real bound on the coordinates of every
point of the domain). -/
theorem convex_extensible_iff_argmin_hole_free {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) :
    (ConvexExtensible f → ∀ p : Fin n → ℝ, HoleFree (ArgMinPerturbed f p)) ∧
    ((∃ R : ℝ, ∀ x : Fin n → ℤ, f x ≠ ⊤ → ∀ i, |(x i : ℝ)| ≤ R) →
      (∀ p : Fin n → ℝ, HoleFree (ArgMinPerturbed f p)) → ConvexExtensible f) := by sorry

end DiscreteConvex.IntegralConvexity
