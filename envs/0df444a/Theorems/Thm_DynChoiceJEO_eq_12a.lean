-- Prove2me | Theorems.Thm_DynChoiceJEO_eq_12a
-- name    : DynChoiceJEO.eq_12a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:01.569133+00:00
-- url     : https://prove2.me/theorems/160f4ff6-4acc-4924-a665-54038657f5c4
-- title:
--   Eq. (12a) — $\widehat\epsilon=\mathcal R_x+\mathcal R_y$
-- statement:
--   For any function $\Psi$, any sets $X\subseteq\mathbb R^N$, $Y\subseteq\mathbb R^k$, any sequences $x_t,y_t,p_t$ and weights $\theta_t$,
--
--   $$\widehat\epsilon\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big)=\mathcal R_x\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big)+\mathcal R_y\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big),$$
--
--   with $\mathcal R_x,\mathcal R_y$ from (12b), (12c). The error term of Theorem 1 thus splits into a primal and a dual regret, each controlled by an online convex optimization algorithm.
--
--   Differences from the source:
--   - encoding: X ⊆ ℝᴺ, Y ⊆ ℝᵏ → X : Set (Fin N → ℝ), Y : Set (Fin k → ℝ); reason: Lean's standard model of Euclidean space; same instances
--   - encoding: index set [T] = {1,…,T} → Fin T = {0,…,T−1}; reason: reindexing; same sequences
--   - encoding: max / min over Y, X → real sSup / sInf of the image; reason: the identity holds for whatever real values the sSup and sInf take, and they are the paper's max/min whenever these exist
--   - generalization: p, p_t in the paper's parameter space (empirical frequency vectors in the application) → an arbitrary type P; reason: no structure of the data space is used; specializes to the paper's parameter space
--   - generalization: standing assumptions of §3 (X, Y convex compact; Ψ convex-concave) → not assumed; reason: the identity is algebraic and holds for every Ψ, X, Y and weights; it specializes to the paper's setting
--   - encoding: Ψ(x,y;p) on X × Y → a total function Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ; reason: a Ψ given on X × Y extends arbitrarily off it, and convexity and concavity are only asked on X and Y; same instances
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eqs. (12a)–(12c), p.13

import Mathlib
import Definitions.Def_DynChoiceJEO_epsHat
import Definitions.Def_DynChoiceJEO_Rx
import Definitions.Def_DynChoiceJEO_Ry

namespace DynChoiceJEO

/-- **Eq. (12a): `ε̂ = R_x + R_y`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (12a), p.13: "ϵ̂({x_t,y_t;p_t,θ_t}_{t∈[T]}) = R_x({x_t,y_t;p_t,θ_t}_{t∈[T]})
+ R_y({x_t,y_t;p_t,θ_t}_{t∈[T]})", with `R_x`, `R_y` from (12b), (12c).

The error term `ε̂` of (11a) splits into the primal regret `R_x` and the dual regret `R_y`.

**Formalization Note** The identity is stated for all `Ψ`, `X`, `Y`, sequences and weights,
without the standing assumptions of §3, which it does not need. `[T]` is `Fin T`. -/
theorem eq_12a {N k T : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ)) (x : Fin T → Fin N → ℝ)
    (y : Fin T → Fin k → ℝ) (pt : Fin T → P) (θ : Fin T → ℝ) :
    epsHat Ψ X Y x y pt θ = Rx Ψ X x y pt θ + Ry Ψ Y x y pt θ := by sorry

end DynChoiceJEO
