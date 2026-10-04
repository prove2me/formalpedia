-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_lemma1_strictConvex_bijection
-- name    : EntropicBarrier.Universal.lemma1_strictConvex_bijection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:02:45.248985+00:00
-- url     : https://prove2.me/theorems/3656081a-3f98-43e4-acdc-a786492cdb2d
-- title:
--   Lemma 1 (i)–(ii) — $f$ and $f^*$ are strictly convex and $\nabla f^*$ is a bijection $\operatorname{int}(\mathcal K)\to\mathbb R^n$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body, $f$ its log-Laplace transform and $f^*$ its entropic barrier. Then
--
--   1. $f$ is strictly convex on $\mathbb R^n$ and $f^*$ is strictly convex on $\operatorname{int}(\mathcal K)$;
--   2. the map $\theta(\cdot)=\nabla f^*(\cdot)$ is a bijection from $\operatorname{int}(\mathcal K)$ onto $\mathbb R^n$.
--
--   These are parts (i) and (ii) of Lemma 1, the duality facts on which the rest of the proof rests.
--
--   **Formalization Note** $\nabla f^*$ is Mathlib's `gradient`; the bijection is `Set.BijOn` from `interior K` onto `Set.univ`.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 5, Lemma 1 (i)-(ii)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem lemma1_strictConvex_bijection {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    StrictConvexOn ℝ Set.univ (logPartition K) ∧
      StrictConvexOn ℝ (interior K) (entropicBarrier K) ∧
      Set.BijOn (gradient (entropicBarrier K)) (interior K) Set.univ := by sorry

end EntropicBarrier.Universal
