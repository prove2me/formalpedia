-- Prove2me | Theorems.Thm_DynChoiceJEO_theorem_1
-- name    : DynChoiceJEO.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:41.762434+00:00
-- url     : https://prove2.me/theorems/8b39e2e1-dcfc-4689-aeb9-f9ebf4f61249
-- title:
--   Theorem 1 — the SP gap of the averages is at most $\widehat\epsilon+\epsilon^\circ+\epsilon^\bullet$
-- statement:
--   Throughout, $X\subseteq\mathbb R^N$ and $Y\subseteq\mathbb R^k$ are convex compact sets and $\Psi(x,y;q)$ is a real function that, for every data value $q$, is convex in $x\in X$ and concave in $y\in Y$ (the standing assumptions of §3).
--
--   Let $(x_t,y_t)\in X\times Y$ for $t\in[T]$ be a primal-dual sequence, $\theta_t\ge0$ weights with $\Theta_T>0$, and $\bar x^\theta_T,\bar y^\theta_T$ the averages (10). Then for any data sequence $p_t$ and any data value $p$,
--
--   $$\epsilon^\Psi_{\mathrm{sad}}(\bar x^\theta_T,\bar y^\theta_T;p)\le\widehat\epsilon\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big)+\epsilon^\circ\big(\{x_t;p_t,\theta_t\}_{t\in[T]};p\big)+\epsilon^\bullet\big(\{y_t;p_t,\theta_t\}_{t\in[T]};p\big),$$
--
--   with $\widehat\epsilon,\epsilon^\circ,\epsilon^\bullet$ from (11a)–(11c).
--
--   The theorem certifies the SP gap on the true data $p$ using only the observed data $p_t$: $\widehat\epsilon$ is controlled by the choice of the sequence, while $\epsilon^\circ,\epsilon^\bullet$ are the price of estimation.
--
--   **Formalization Note** The bound is stated when the suprema defining $\epsilon^\circ$ and $\epsilon^\bullet$ are finite (bounded-above images); otherwise the paper's right side is $+\infty$ and the claim is empty.
--
--   Differences from the source:
--   - encoding: X ⊆ ℝᴺ, Y ⊆ ℝᵏ → X : Set (Fin N → ℝ), Y : Set (Fin k → ℝ); reason: Lean's standard model of Euclidean space; same instances
--   - encoding: index set [T] = {1,…,T} → Fin T = {0,…,T−1}; reason: reindexing; same sequences
--   - encoding: max / min over Y, X → real sSup / sInf of the image; reason: the sets are nonempty and bounded under the standing assumptions, so the values agree with the paper's max/min whenever these exist (and are the sup/inf otherwise)
--   - encoding: Θ_T = Σθ_t used as a divisor (T ≥ 1) → hypothesis 0 < ∑ t, θ t; reason: excludes only Θ_T = 0, where 1/Θ_T and the averages (10) are undefined; implies T ≥ 1
--   - encoding: ε° and ε• are max's that may be +∞ → BddAbove of the two images defining ε° and ε•; reason: excludes only the case ε° = +∞ or ε• = +∞, where the paper's bound is trivially true and Lean's real sSup would be 0
--   - generalization: p, p_t in the paper's parameter space (empirical frequency vectors in the application) → an arbitrary type P; reason: no structure of the data space is used; specializes to the paper's parameter space
--   - reading: ε^Ψ_sad defined by the two lines of (9), asserted equal via Sion's theorem → the second line, max_Y Ψ(x̄,·;p) − min_X Ψ(·,ȳ;p); reason: the second line exceeds the first by P(p) − D(p) ≥ 0 (weak duality), so bounding it is the stronger statement, and it needs no minimax theorem
--   - reading: "primal-dual sequence" {x_t,y_t} → hypotheses ∀ t, x t ∈ X and ∀ t, y t ∈ Y; reason: the framework generates (x_t,y_t) ∈ X × Y (p.10, step 2)
--   - reading: "weight sequence" with no sign stated on the page of the theorem → hypothesis ∀ t, 0 ≤ θ t; reason: the framework's weights are non-negative (p.10, step 3) and the proof of Theorem 1 uses θ_t/Θ_T as convex combination weights
--   - encoding: Ψ(x,y;p) on X × Y → a total function Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ; reason: a Ψ given on X × Y extends arbitrarily off it, and convexity and concavity are only asked on X and Y; same instances
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Theorem 1 and eqs. (11a)–(11c), p.11

import Mathlib
import Definitions.Def_DynChoiceJEO_wavg
import Definitions.Def_DynChoiceJEO_sadGap
import Definitions.Def_DynChoiceJEO_epsHat
import Definitions.Def_DynChoiceJEO_epsCirc
import Definitions.Def_DynChoiceJEO_epsBullet

namespace DynChoiceJEO

/-- **Theorem 1: the SP gap of the averages is at most `ε̂ + ε° + ε•`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, Theorem 1, p.11: "For given T ≥ 1, primal-dual sequence {x_t,y_t}_{t∈[T]} and weight
sequence {θ_t}_{t∈[T]}, let x̄_T^θ, ȳ_T^θ be defined as in (10). Then, given any data sequence
{p_t}_{t∈[T]}, we have ϵ^Ψ_sad(x̄_T^θ, ȳ_T^θ;p) ≤ ϵ̂({x_t,y_t;p_t,θ_t}_{t∈[T]})
+ ϵ◦({x_t;p_t,θ_t}_{t∈[T]}) + ϵ•({y_t;p_t,θ_t}_{t∈[T]})", with (11a)–(11c).

For `(x_t,y_t) ∈ X × Y`, weights `θ_t ≥ 0` with `Θ_T > 0`, any data sequence `p_t` and true
data `p`: `ε_sad(x̄,ȳ;p) ≤ ε̂ + ε°(·;p) + ε•(·;p)`.

**Formalization Note** ℝᴺ, ℝᵏ are `Fin N → ℝ`, `Fin k → ℝ`; the data space is an arbitrary
type `P`. The standing assumptions of §3 (p.9) are binders: `X`, `Y` convex and compact, and for
every data value `q` the map `Ψ(·,y;q)` is convex on `X` for `y ∈ Y` and `Ψ(x,·;q)` is concave on
`Y` for `x ∈ X`. `[T]` is `Fin T` (0-based). The weights satisfy `θ_t ≥ 0` (p.10, step 3) and
`Θ_T = ∑ θ_t > 0` (nondegeneracy; it implies `T ≥ 1`). max/min are `sSup`/`sInf` of images.
The SP gap is the second line of (9). The suprema defining `ε°` and `ε•` are of differences of
concave (resp. convex) functions and may be `+∞`, in which case the paper's bound is trivially
true; the hypotheses `hbddCirc`, `hbddBullet` (`BddAbove` of those two images) exclude exactly
that case, where Lean's real `sSup` would be `0`. -/
theorem theorem_1 {N k T : ℕ} {P : Type*}
    (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ))
    (hXc : Convex ℝ X) (hXk : IsCompact X) (hYc : Convex ℝ Y) (hYk : IsCompact Y)
    (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (hΨx : ∀ q : P, ∀ y ∈ Y, ConvexOn ℝ X (fun x => Ψ x y q))
    (hΨy : ∀ q : P, ∀ x ∈ X, ConcaveOn ℝ Y (fun y => Ψ x y q))
    (x : Fin T → Fin N → ℝ) (y : Fin T → Fin k → ℝ) (hx : ∀ t, x t ∈ X) (hy : ∀ t, y t ∈ Y)
    (θ : Fin T → ℝ) (hθ : ∀ t, 0 ≤ θ t) (hΘ : 0 < ∑ t, θ t) (pt : Fin T → P) (p : P)
    (hbddCirc : BddAbove
      ((fun y' => (∑ t, θ t)⁻¹ * ∑ t, θ t * (Ψ (x t) y' p - Ψ (x t) y' (pt t))) '' Y))
    (hbddBullet : BddAbove
      ((fun x' => (∑ t, θ t)⁻¹ * ∑ t, θ t * (Ψ x' (y t) (pt t) - Ψ x' (y t) p)) '' X)) :
    sadGap Ψ X Y (wavg θ x) (wavg θ y) p ≤
      epsHat Ψ X Y x y pt θ + epsCirc Ψ Y x pt θ p + epsBullet Ψ X y pt θ p := by sorry

end DynChoiceJEO
