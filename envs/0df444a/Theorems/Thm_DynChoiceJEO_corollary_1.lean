-- Prove2me | Theorems.Thm_DynChoiceJEO_corollary_1
-- name    : DynChoiceJEO.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:18.537261+00:00
-- url     : https://prove2.me/theorems/1530b72c-28ac-43dc-880f-3eb6c088c407
-- title:
--   Corollary 1 — primal optimality gap of the weighted average is at most $\mathcal R_y+\epsilon^\circ+\epsilon^\bullet$
-- statement:
--   Throughout, $X\subseteq\mathbb R^N$ and $Y\subseteq\mathbb R^k$ are convex compact sets and $\Psi(x,y;q)$ is a real function that, for every data value $q$, is convex in $x\in X$ and concave in $y\in Y$ (the standing assumptions of §3).
--
--   Let $y_t\in Y$, data $p_t$ and weights $\theta_t\ge0$ with $\Theta_T=\sum_{t\in[T]}\theta_t>0$ be arbitrary sequences, and let $p$ be the true data. Suppose that for each $t\in[T]$,
--
--   $$x_t\in\arg\min_{x\in X}\Psi(x,y_t;p_t),$$
--
--   and let $\bar x^\theta_T:=\frac1{\Theta_T}\sum_{t\in[T]}\theta_tx_t$. Then, with $f(x;p)=\max_{y\in Y}\Psi(x,y;p)$,
--
--   $$f(\bar x^\theta_T;p)-\min_{x\in X}f(x;p)\le\mathcal R_y\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big)+\epsilon^\circ\big(\{x_t;p_t,\theta_t\}_{t\in[T]};p\big)+\epsilon^\bullet\big(\{y_t;p_t,\theta_t\}_{t\in[T]};p\big).$$
--
--   With primal-oracle steps, the primal optimality gap on the true data is bounded by the dual regret alone plus the price of estimation. In the choice-model application each oracle step is a linear program over the choice-probability polytope whose solution is a vertex, so $\bar x^\theta_T$ comes with an explicit sparse distribution over rankings.
--
--   **Formalization Note** $x_t\in\arg\min$ means $x_t\in X$ and $\Psi(x_t,y_t;p_t)\le\Psi(x',y_t;p_t)$ for all $x'\in X$. The bound is stated when the suprema defining $\epsilon^\circ$ and $\epsilon^\bullet$ are finite; otherwise the paper's right side is $+\infty$.
--
--   Differences from the source:
--   - encoding: X ⊆ ℝᴺ, Y ⊆ ℝᵏ → X : Set (Fin N → ℝ), Y : Set (Fin k → ℝ); reason: Lean's standard model of Euclidean space; same instances
--   - encoding: index set [T] = {1,…,T} → Fin T = {0,…,T−1}; reason: reindexing; same sequences
--   - encoding: max / min over Y, X → real sSup / sInf of the image; reason: the sets are nonempty and bounded under the standing assumptions, so the values agree with the paper's max/min whenever these exist (and are the sup/inf otherwise)
--   - encoding: Θ_T = Σθ_t used as a divisor (T ≥ 1) → hypothesis 0 < ∑ t, θ t; reason: excludes only Θ_T = 0, where 1/Θ_T and the averages (10) are undefined; implies T ≥ 1
--   - encoding: ε° and ε• are max's that may be +∞ → BddAbove of the two images defining ε° and ε•; reason: excludes only the case ε° = +∞ or ε• = +∞, where the paper's bound is trivially true and Lean's real sSup would be 0
--   - generalization: p, p_t in the paper's parameter space (empirical frequency vectors in the application) → an arbitrary type P; reason: no structure of the data space is used; specializes to the paper's parameter space
--   - reading: "arbitrary dual … sequences" → hypothesis ∀ t, y t ∈ Y; reason: a dual sequence lies in Y (p.10, step 2); the data and the values of y_t inside Y stay arbitrary
--   - reading: "arbitrary … weight sequences" → hypothesis ∀ t, 0 ≤ θ t; reason: the framework's weights are non-negative (p.10, step 3); Theorem 1 and Lemma 1, which give the corollary, need them
--   - encoding: Ψ(x,y;p) on X × Y → a total function Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ; reason: a Ψ given on X × Y extends arbitrarily off it, and convexity and concavity are only asked on X and Y; same instances
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Corollary 1, p.14

import Mathlib
import Definitions.Def_DynChoiceJEO_wavg
import Definitions.Def_DynChoiceJEO_fval
import Definitions.Def_DynChoiceJEO_Ry
import Definitions.Def_DynChoiceJEO_epsCirc
import Definitions.Def_DynChoiceJEO_epsBullet

namespace DynChoiceJEO

/-- **Corollary 1: with primal-oracle steps, the primal optimality gap of the weighted average is
at most `R_y + ε° + ε•`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, Corollary 1, p.14: "Let {y_t}_{t∈[T]}, {p_t}_{t∈[T]} and {θ_t}_{t∈[T]} be arbitrary dual,
data and weight sequences. Suppose that for each t ∈ [T], x_t ∈ arg min_{x∈X} Ψ(x,y_t;p_t). Denote
x̄_T^θ := (1/Θ_T) ∑_{t∈[T]} θ_t x_t. Then, we have f(x̄_T^θ;p) − min_{x∈X} f(x;p)
≤ R_y({x_t,y_t;p_t,θ_t}_{t∈[T]}) + ϵ◦({x_t;p_t,θ_t}_{t∈[T]};p) + ϵ•({y_t;p_t,θ_t}_{t∈[T]};p)."

**Formalization Note** ℝᴺ, ℝᵏ are `Fin N → ℝ`, `Fin k → ℝ`; the data space is an arbitrary
type `P`. The standing assumptions of §3 (p.9) are binders: `X`, `Y` convex and compact, and for
every data value `q` the map `Ψ(·,y;q)` is convex on `X` for `y ∈ Y` and `Ψ(x,·;q)` is concave on
`Y` for `x ∈ X`. `[T]` is `Fin T` (0-based). The weights satisfy `θ_t ≥ 0` (p.10, step 3) and
`Θ_T = ∑ θ_t > 0` (nondegeneracy; it implies `T ≥ 1`). max/min are `sSup`/`sInf` of images.
`x_t ∈ argmin_{x∈X} Ψ(x,y_t;p_t)` is `x t ∈ X` together with `Ψ(x_t,y_t;p_t) ≤ Ψ(x',y_t;p_t)`
for all `x' ∈ X`; the dual sequence lies in `Y` (step 2, p.10). `f = fval` is `max_{y∈Y} Ψ(x,y;p)`.
The suprema defining `ε°` and `ε•` may be `+∞` (then the paper's bound is trivially true);
`hbddCirc`, `hbddBullet` (`BddAbove` of those two images) exclude exactly that case, where
Lean's real `sSup` would be `0`. -/
theorem corollary_1 {N k T : ℕ} {P : Type*}
    (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ))
    (hXc : Convex ℝ X) (hXk : IsCompact X) (hYc : Convex ℝ Y) (hYk : IsCompact Y)
    (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (hΨx : ∀ q : P, ∀ y ∈ Y, ConvexOn ℝ X (fun x => Ψ x y q))
    (hΨy : ∀ q : P, ∀ x ∈ X, ConcaveOn ℝ Y (fun y => Ψ x y q))
    (y : Fin T → Fin k → ℝ) (hy : ∀ t, y t ∈ Y) (pt : Fin T → P) (p : P)
    (θ : Fin T → ℝ) (hθ : ∀ t, 0 ≤ θ t) (hΘ : 0 < ∑ t, θ t)
    (x : Fin T → Fin N → ℝ)
    (hx : ∀ t, x t ∈ X ∧ ∀ x' ∈ X, Ψ (x t) (y t) (pt t) ≤ Ψ x' (y t) (pt t))
    (hbddCirc : BddAbove
      ((fun y' => (∑ t, θ t)⁻¹ * ∑ t, θ t * (Ψ (x t) y' p - Ψ (x t) y' (pt t))) '' Y))
    (hbddBullet : BddAbove
      ((fun x' => (∑ t, θ t)⁻¹ * ∑ t, θ t * (Ψ x' (y t) (pt t) - Ψ x' (y t) p)) '' X)) :
    fval Ψ Y (wavg θ x) p - sInf ((fun x' => fval Ψ Y x' p) '' X) ≤
      Ry Ψ Y x y pt θ + epsCirc Ψ Y x pt θ p + epsBullet Ψ X y pt θ p := by sorry

end DynChoiceJEO
