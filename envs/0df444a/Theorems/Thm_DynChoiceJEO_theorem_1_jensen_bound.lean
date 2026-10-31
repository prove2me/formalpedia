-- Prove2me | Theorems.Thm_DynChoiceJEO_theorem_1_jensen_bound
-- name    : DynChoiceJEO.theorem_1_jensen_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:41.557124+00:00
-- url     : https://prove2.me/theorems/92a48058-2f5e-4583-b1bc-a963b191a62f
-- title:
--   Proof of Theorem 1 — Jensen bound on the SP gap of the weighted averages
-- statement:
--   Throughout, $X\subseteq\mathbb R^N$ and $Y\subseteq\mathbb R^k$ are convex compact sets and $\Psi(x,y;q)$ is a real function that, for every data value $q$, is convex in $x\in X$ and concave in $y\in Y$ (the standing assumptions of §3).
--
--   Let $(x_t,y_t)\in X\times Y$ for $t\in[T]$, let $\theta_t\ge0$ with $\Theta_T=\sum_t\theta_t>0$, let $\bar x^\theta_T,\bar y^\theta_T$ be the weighted averages (10), and let $p$ be any data value. Then
--
--   $$\epsilon^\Psi_{\mathrm{sad}}(\bar x^\theta_T,\bar y^\theta_T;p)\le\max_{y\in Y}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x_t,y;p)-\min_{x\in X}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x,y_t;p).$$
--
--   This is the first step of the proof of Theorem 1: the weights $\theta_t/\Theta_T$ form a convex combination, so the convex-concave structure of $\Psi$ bounds the gap at the averages by the averaged gap.
--
--   Differences from the source:
--   - encoding: X ⊆ ℝᴺ, Y ⊆ ℝᵏ → X : Set (Fin N → ℝ), Y : Set (Fin k → ℝ); reason: Lean's standard model of Euclidean space; same instances
--   - encoding: index set [T] = {1,…,T} → Fin T = {0,…,T−1}; reason: reindexing; same sequences
--   - encoding: max / min over Y, X → real sSup / sInf of the image; reason: the sets are nonempty and bounded under the standing assumptions, so the values agree with the paper's max/min whenever these exist (and are the sup/inf otherwise)
--   - encoding: Θ_T = Σθ_t used as a divisor (T ≥ 1) → hypothesis 0 < ∑ t, θ t; reason: excludes only Θ_T = 0, where 1/Θ_T and the averages (10) are undefined; implies T ≥ 1
--   - generalization: p, p_t in the paper's parameter space (empirical frequency vectors in the application) → an arbitrary type P; reason: no structure of the data space is used; specializes to the paper's parameter space
--   - reading: ε^Ψ_sad defined by the two lines of (9), asserted equal via Sion's theorem → the second line, max_Y Ψ(x̄,·;p) − min_X Ψ(·,ȳ;p); reason: the second line exceeds the first by P(p) − D(p) ≥ 0 (weak duality), so bounding it is the stronger statement, and it needs no minimax theorem
--   - reading: "primal-dual sequence" {x_t,y_t} → hypotheses ∀ t, x t ∈ X and ∀ t, y t ∈ Y; reason: the framework generates (x_t,y_t) ∈ X × Y (p.10, step 2)
--   - reading: "weight sequence" with no sign stated on the page of the theorem → hypothesis ∀ t, 0 ≤ θ t; reason: the framework's weights are non-negative (p.10, step 3) and the proof of Theorem 1 uses θ_t/Θ_T as convex combination weights
--   - encoding: Ψ(x,y;p) on X × Y → a total function Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ; reason: a Ψ given on X × Y extends arbitrarily off it, and convexity and concavity are only asked on X and Y; same instances
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, proof of Theorem 1, p.ec1 (PDF 23), "we get the standard bound"

import Mathlib
import Definitions.Def_DynChoiceJEO_wavg
import Definitions.Def_DynChoiceJEO_sadGap

namespace DynChoiceJEO

/-- **Proof of Theorem 1: the Jensen ("standard") bound on the SP gap of the averages.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, proof of Theorem 1, p.ec1 (PDF 23): "First, notice that {θ_t/Θ_T}_{t∈[T]} form a set of
convex combination weights. Thus, using the convex-concave structure of Ψ(·,·;p) and the
definition of ϵ^Ψ_sad(x̄_T^θ, ȳ_T^θ;p) in (9), we get the standard bound
ϵ^Ψ_sad(x̄_T^θ, ȳ_T^θ;p) ≤ max_{y∈Y} (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x_t,y;p)
− min_{x∈X} (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x,y_t;p)."

For a primal-dual sequence `(x_t,y_t) ∈ X × Y`, nonnegative weights with `Θ_T > 0` and any
data `p`, the SP gap (9) of the weighted averages (10) is at most the sup over `Y` of the
averaged `Ψ(x_t,·;p)` minus the inf over `X` of the averaged `Ψ(·,y_t;p)`.

**Formalization Note** ℝᴺ, ℝᵏ are `Fin N → ℝ`, `Fin k → ℝ`; the data space is an arbitrary
type `P`. The standing assumptions of §3 (p.9) are binders: `X`, `Y` convex and compact, and for
every data value `q` the map `Ψ(·,y;q)` is convex on `X` for `y ∈ Y` and `Ψ(x,·;q)` is concave on
`Y` for `x ∈ X`. `[T]` is `Fin T` (0-based). The weights satisfy `θ_t ≥ 0` (p.10, step 3) and
`Θ_T = ∑ θ_t > 0` (nondegeneracy; it implies `T ≥ 1`). max/min are `sSup`/`sInf` of images.
The SP gap is the second line of (9) (`sadGap`). -/
theorem theorem_1_jensen_bound {N k T : ℕ} {P : Type*}
    (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ))
    (hXc : Convex ℝ X) (hXk : IsCompact X) (hYc : Convex ℝ Y) (hYk : IsCompact Y)
    (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (hΨx : ∀ q : P, ∀ y ∈ Y, ConvexOn ℝ X (fun x => Ψ x y q))
    (hΨy : ∀ q : P, ∀ x ∈ X, ConcaveOn ℝ Y (fun y => Ψ x y q))
    (x : Fin T → Fin N → ℝ) (y : Fin T → Fin k → ℝ) (hx : ∀ t, x t ∈ X) (hy : ∀ t, y t ∈ Y)
    (θ : Fin T → ℝ) (hθ : ∀ t, 0 ≤ θ t) (hΘ : 0 < ∑ t, θ t) (p : P) :
    sadGap Ψ X Y (wavg θ x) (wavg θ y) p ≤
      sSup ((fun y' => (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ (x t) y' p) '' Y)
        - sInf ((fun x' => (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ x' (y t) p) '' X) := by sorry

end DynChoiceJEO
