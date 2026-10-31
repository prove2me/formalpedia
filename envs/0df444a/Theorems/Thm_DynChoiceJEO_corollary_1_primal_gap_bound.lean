-- Prove2me | Theorems.Thm_DynChoiceJEO_corollary_1_primal_gap_bound
-- name    : DynChoiceJEO.corollary_1_primal_gap_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:45.429446+00:00
-- url     : https://prove2.me/theorems/126c2d07-2ab2-4a0f-ab10-5f34f522f7d7
-- title:
--   Proof of Corollary 1 — the primal optimality gap is at most the SP gap
-- statement:
--   Throughout, $X\subseteq\mathbb R^N$ and $Y\subseteq\mathbb R^k$ are convex compact sets and $\Psi(x,y;q)$ is a real function that, for every data value $q$, is convex in $x\in X$ and concave in $y\in Y$ (the standing assumptions of §3).
--
--   Write $f$ and $g$ for the primal and dual objectives (7a), (7b). For every $\bar x\in X$, $\bar y\in Y$ and data value $p$,
--
--   $$f(\bar x;p)-\min_{x\in X}f(x;p)+\max_{y\in Y}g(y;p)-g(\bar y;p)\ \ge\ f(\bar x;p)-\min_{x\in X}f(x;p).$$
--
--   The left side is the SP gap in the form of the first line of (9); the inequality says that the optimality gap of the dual problem $\mathcal D(p)$ is nonnegative. It is the last step of the proof of Corollary 1.
--
--   Differences from the source:
--   - encoding: X ⊆ ℝᴺ, Y ⊆ ℝᵏ → X : Set (Fin N → ℝ), Y : Set (Fin k → ℝ); reason: Lean's standard model of Euclidean space; same instances
--   - encoding: max / min over Y, X → real sSup / sInf of the image; reason: the sets are nonempty and bounded under the standing assumptions, so the values agree with the paper's max/min whenever these exist (and are the sup/inf otherwise)
--   - generalization: p, p_t in the paper's parameter space (empirical frequency vectors in the application) → an arbitrary type P; reason: no structure of the data space is used; specializes to the paper's parameter space
--   - generalization: the pair (x̄_T^θ, ȳ_T^θ) of averages (10) → an arbitrary pair x̄ ∈ X, ȳ ∈ Y; reason: the step uses only x̄ ∈ X, ȳ ∈ Y; the averages lie in X × Y by convexity
--   - reading: the display ϵ_sad(x̄,ȳ;p) = f(x̄;p) − min_X f + max_Y g − g(ȳ;p) ≥ f(x̄;p) − min_X f → the inequality between the written-out first line of (9) and f(x̄;p) − min_X f, with no mention of sadGap; reason: the equality is the definition of ϵ_sad by the first line of (9), while the mission's sadGap is the second line; the second line is at least the first by weak duality, so nothing is lost
--   - encoding: Ψ(x,y;p) on X × Y → a total function Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ; reason: a Ψ given on X × Y extends arbitrarily off it, and convexity and concavity are only asked on X and Y; same instances
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, proof of Corollary 1, p.ec2 (PDF 24)

import Mathlib
import Definitions.Def_DynChoiceJEO_fval
import Definitions.Def_DynChoiceJEO_gval

namespace DynChoiceJEO

/-- **Proof of Corollary 1: the primal optimality gap is at most the SP gap (first line of (9)).**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, proof of Corollary 1, p.ec2 (PDF 24): "ϵ^Ψ_sad(x̄_T^θ, ȳ_T^θ;p) = f(x̄_T^θ;p) − min_{x∈X} f(x;p)
+ max_{y∈Y} g(y,p) − g(ȳ_T^θ;p) ≥ f(x̄_T^θ;p) − min_{x∈X} f(x;p) since the optimality gap for the
dual problem D(p) in (7b) is always non-negative."

For any `x̄ ∈ X`, `ȳ ∈ Y` and data `p`:
`f(x̄;p) − min_{x∈X} f(x;p) + max_{y∈Y} g(y;p) − g(ȳ;p) ≥ f(x̄;p) − min_{x∈X} f(x;p)`,
with `f = fval` (7a) and `g = gval` (7b).

**Formalization Note** ℝᴺ, ℝᵏ are `Fin N → ℝ`, `Fin k → ℝ`; the data space is an arbitrary
type `P`. The standing assumptions of §3 (p.9) are binders: `X`, `Y` convex and compact, and for
every data value `q` the map `Ψ(·,y;q)` is convex on `X` for `y ∈ Y` and `Ψ(x,·;q)` is concave on
`Y` for `x ∈ X`. max/min are `sSup`/`sInf` of images. The left side is the first line of (9),
written out with `P(p) = min_X f` and `D(p) = max_Y g`, exactly as in the displayed step. The step
is stated for an arbitrary pair `(x̄,ȳ) ∈ X × Y`; the paper applies it to the averages (10). -/
theorem corollary_1_primal_gap_bound {N k : ℕ} {P : Type*}
    (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ))
    (hXc : Convex ℝ X) (hXk : IsCompact X) (hYc : Convex ℝ Y) (hYk : IsCompact Y)
    (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (hΨx : ∀ q : P, ∀ y ∈ Y, ConvexOn ℝ X (fun x => Ψ x y q))
    (hΨy : ∀ q : P, ∀ x ∈ X, ConcaveOn ℝ Y (fun y => Ψ x y q))
    (xbar : Fin N → ℝ) (ybar : Fin k → ℝ) (hxbar : xbar ∈ X) (hybar : ybar ∈ Y) (p : P) :
    fval Ψ Y xbar p - sInf ((fun x' => fval Ψ Y x' p) '' X) ≤
      fval Ψ Y xbar p - sInf ((fun x' => fval Ψ Y x' p) '' X)
        + sSup ((fun y' => gval Ψ X y' p) '' Y) - gval Ψ X ybar p := by sorry

end DynChoiceJEO
