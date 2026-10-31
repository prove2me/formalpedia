-- Prove2me | Theorems.Thm_DynChoiceJEO_lemma_1
-- name    : DynChoiceJEO.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:57.254546+00:00
-- url     : https://prove2.me/theorems/8183bad2-ea3d-4cfb-8c64-478fed833f87
-- title:
--   Lemma 1 — primal-oracle steps give $\mathcal R_x\le0$
-- statement:
--   Let $y_t\in\mathbb R^k$, data $p_t$ and weights $\theta_t\ge0$ with $\Theta_T>0$ be arbitrary sequences, $t\in[T]$. Suppose that for each $t$, $x_t$ is obtained by the primal oracle step (13),
--
--   $$x_t\in\arg\min_{x\in X}\Psi(x,y_t;p_t).$$
--
--   Then
--
--   $$\mathcal R_x\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big)=\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x_t,y_t;p_t)-\min_{x\in X}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x,y_t;p_t)\le0.$$
--
--   A lookahead primal step thus costs no primal regret, which removes $\mathcal R_x$ from the bound of Theorem 1.
--
--   **Formalization Note** $x_t\in\arg\min$ means $x_t\in X$ and $\Psi(x_t,y_t;p_t)\le\Psi(x',y_t;p_t)$ for all $x'\in X$.
--
--   Differences from the source:
--   - encoding: X ⊆ ℝᴺ, Y ⊆ ℝᵏ → X : Set (Fin N → ℝ), Y : Set (Fin k → ℝ); reason: Lean's standard model of Euclidean space; same instances
--   - encoding: index set [T] = {1,…,T} → Fin T = {0,…,T−1}; reason: reindexing; same sequences
--   - encoding: min over X → real sInf of the image; reason: the image is nonempty (T ≥ 1, x_t ∈ X) and bounded below by the first term of R_x, so sInf is the infimum, and it is the paper's min whenever that exists
--   - encoding: Θ_T = Σθ_t used as a divisor (T ≥ 1) → hypothesis 0 < ∑ t, θ t; reason: excludes only Θ_T = 0, where 1/Θ_T and the averages (10) are undefined; implies T ≥ 1
--   - generalization: p, p_t in the paper's parameter space (empirical frequency vectors in the application) → an arbitrary type P; reason: no structure of the data space is used; specializes to the paper's parameter space
--   - generalization: standing assumptions of §3 (X, Y convex compact; Ψ convex-concave) → not assumed; reason: the lemma uses only the minimality of each x_t and θ_t ≥ 0; it specializes to the paper's setting
--   - reading: "arbitrary … weight sequences" → hypothesis ∀ t, 0 ≤ θ t; reason: the framework's weights are non-negative (p.10, step 3); with negative weights the lemma fails (X = [0,1], Y = [−1,1], Ψ = xy, y = (1,−1), x = (0,1), θ = (2,−1) gives R_x = 1)
--   - encoding: Ψ(x,y;p) on X × Y → a total function Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ; reason: a Ψ given on X × Y extends arbitrarily off it, and convexity and concavity are only asked on X and Y; same instances
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Lemma 1 and eq. (13), p.13

import Mathlib
import Definitions.Def_DynChoiceJEO_Rx

namespace DynChoiceJEO

/-- **Lemma 1: primal-oracle steps have nonpositive primal regret.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, Lemma 1, p.13: "Let {y_t}_{t∈[T]}, {p_t}_{t∈[T]} and {θ_t}_{t∈[T]} be arbitrary dual, data
and weight sequences. Suppose that for each t ∈ [T], x_t is obtained via (13). Then, we have
R_x({x_t,y_t;p_t,θ_t}_{t∈[T]}) = (1/Θ_T) ∑ θ_t Ψ(x_t,y_t;p_t) − min_{x∈X} (1/Θ_T) ∑ θ_t Ψ(x,y_t;p_t)
≤ 0", where (13) is "x_t ∈ arg min_{x∈X} Ψ(x,y_t;p_t)".

**Formalization Note** `x_t ∈ argmin_{x∈X} Ψ(x,y_t;p_t)` is `x t ∈ X` together with
`Ψ(x_t,y_t;p_t) ≤ Ψ(x',y_t;p_t)` for all `x' ∈ X`. Weights satisfy `θ_t ≥ 0` (p.10, step 3) and
`Θ_T > 0`. The lemma is stated without the convexity/compactness standing assumptions of §3,
which it does not use; `y_t`, `p_t` are arbitrary. `[T]` is `Fin T`; min is `sInf`. -/
theorem lemma_1 {N k T : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (X : Set (Fin N → ℝ)) (x : Fin T → Fin N → ℝ) (y : Fin T → Fin k → ℝ) (pt : Fin T → P)
    (hx : ∀ t, x t ∈ X ∧ ∀ x' ∈ X, Ψ (x t) (y t) (pt t) ≤ Ψ x' (y t) (pt t))
    (θ : Fin T → ℝ) (hθ : ∀ t, 0 ≤ θ t) (hΘ : 0 < ∑ t, θ t) :
    Rx Ψ X x y pt θ ≤ 0 := by sorry

end DynChoiceJEO
