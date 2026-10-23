-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_3_1
-- name    : BoxTDIMinMax.Separable.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:32.097213+00:00
-- url     : https://prove2.me/theorems/7a8b30fb-b3c3-409b-9b50-2bcf599ba941
-- title:
--   Proposition 3.1, p. 12 — a φ-fitting pair (k∗, ℓ∗) maximizes ℓ∗k − φ(k), (3.5)
-- statement:
--   Let $\varphi:\mathbb Z\to\mathbb Z\cup\{+\infty\}$ be discrete convex and let $(k^*,\ell^*)$ be a $\varphi$-fitting pair of integers, i.e. $\varphi(k^*)$ is finite and $\varphi(k^*)-\varphi(k^*-1)\le\ell^*\le\varphi(k^*+1)-\varphi(k^*)$. Then
--   $$\ell^*k^*-\varphi(k^*)\ \ge\ \ell^*k-\varphi(k)\qquad\text{for every integer } k. \qquad (3.5)$$
--
--   Equivalently, $\ell^*$ is a subgradient of $\varphi$ at $k^*$. Applied coordinatewise, this inequality is the source of weak duality (Lemma 3.2).
--
--   **Formalization Note** The inequality is stated without subtraction as $\varphi(k^*)+\ell^*k\le\varphi(k)+\ell^*k^*$ in $\mathbb Z\cup\{+\infty\}$; it is trivially true when $\varphi(k)=+\infty$. The parenthetical conjugate form $\varphi^\bullet(\ell^*)=\ell^*k^*-\varphi(k^*)$ is not stated, since the discrete conjugate is not defined in this mission.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 12, Proposition 3.1, (3.5)

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 3.1, p. 12, (3.5): for a discrete convex `φ` and a `φ`-fitting pair `(k*, ℓ*)`,
`ℓ* k* - φ(k*) ≥ ℓ* k - φ(k)` for every integer `k`, written without subtraction as
`φ(k*) + ℓ* k ≤ φ(k) + ℓ* k*`. -/
theorem proposition_3_1 (φ : ℤ → WithTop ℤ) (hφ : DiscConvex φ) (kStar lStar : ℤ)
    (hfit : Fitting φ kStar lStar) (k : ℤ) :
    φ kStar + ((lStar * k : ℤ) : WithTop ℤ) ≤ φ k + ((lStar * kStar : ℤ) : WithTop ℤ) := by sorry

end BoxTDIMinMax.Separable
