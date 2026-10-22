-- Prove2me | Theorems.Thm_EntFluctCDS_GreenKubo_lemma_4_4
-- name    : EntFluctCDS.GreenKubo.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:46.154045+00:00
-- url     : https://prove2.me/theorems/bfe731f7-9a53-45cb-8fe9-a094158bded7
-- title:
--   Lemma 4.4 — the symmetry lemma for $C^{1,2}$ functions
-- statement:
--   Let $a(X,Y)$ be real-valued and $C^{1,2}$ on an open neighborhood of $(0,0)$ in $\mathbb R^N\times\mathbb R^N$: its first $X$ and $Y$ partials, second $Y$ partials, and mixed partials in both orders all exist and are continuous. If $a(X,Y)=a(X,X-Y)$ throughout that neighborhood, then for every pair of coordinates $j,k$,
--
--   $$\left.\partial_{X_k}\partial_{Y_j}a\right|_{(0,0)}=-\frac12\left.\partial_{Y_j}\partial_{Y_k}a\right|_{(0,0)}.$$
--
--   The lemma converts a finite-time fluctuation symmetry into a relation between response coefficients and fluctuations.
--
--   **Formalization Note** The $C^{1,2}$ predicate asserts existence of each derivative before using Lean's total derivative operator; no second derivative in $X$ is assumed.
-- source:
--   Jakšić, Pillet & Rey-Bellet, Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, p. 19, Lemma 4.4

import Mathlib
import Definitions.Def_EntFluctCDS_GreenKubo_Family

noncomputable section

namespace EntFluctCDS.GreenKubo

/-- Lemma 4.4, p. 19, for exactly C¹,² partial regularity. -/
theorem lemma_4_4 {N : ℕ}
    (a : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (O : Set ((Fin N → ℝ) × (Fin N → ℝ)))
    (hopen : IsOpen O) (hzero : ((0 : Fin N → ℝ), (0 : Fin N → ℝ)) ∈ O)
    (hreg : IsC12On a O)
    (hsym : ∀ p ∈ O, a p.1 p.2 = a p.1 (p.1 - p.2)) :
    ∀ j k : Fin N,
      partialX (partialY a j) k 0 0 =
        -(1 / 2 : ℝ) * partialY (partialY a k) j 0 0 := by sorry

end EntFluctCDS.GreenKubo
