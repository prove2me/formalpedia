-- Prove2me | Theorems.Thm_BauerleRiederMDP_ConvexModels_proposition_2_4_21
-- name    : BauerleRiederMDP.ConvexModels.proposition_2_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:23:30.640222+00:00
-- url     : https://prove2.me/theorems/19949183-f5b8-4e80-b5d9-8c7b1a48a7f9
-- title:
--   Proposition 2.4.21 — $T_n$ preserves convexity, with a bang-bang maximizer on a polytope
-- statement:
--   Throughout, $E\subset\mathbb R^d$ and $A\subset\mathbb R^m$ are Borel sets carrying the componentwise order, and $(E,A,D_n,Q_n,r_n,g_N)$ is a Markov Decision Model with planning horizon $N$: $D_n\subset E\times A$ are the admissible state–action pairs, $Q_n(\cdot\mid x,a)$ the transition kernels, $r_n$ the one-stage rewards and $g_N$ the terminal reward. The model has an **upper bounding function** $b\ge 0$ (Definition 2.4.1): $r_n^+\le c_r b$, $g_N^+\le c_g b$ and $\int b\,dQ_n(\cdot\mid x,a)\le\alpha_b b(x)$ on $D_n$. Write
--   $$
--   \mathbb B_b^+=\{v:E\to[-\infty,\infty)\text{ measurable}\mid v^+\le c\,b\text{ for some }c\ge 0\},\qquad L_nv(x,a)=r_n(x,a)+\int v(x')\,Q_n(dx'\mid x,a),\qquad T_nv(x)=\sup_{a\in D_n(x)}L_nv(x,a).
--   $$
--   A **maximizer** of $v$ at time $n$ is a decision rule $f\in F_n$ (a measurable $f$ with $f(x)\in D_n(x)$) with $L_nv(x,f(x))=T_nv(x)$ for all $x$.
--
--   Let $v\in\mathbb B_b^+$, fix $n<N$, and suppose
--
--   1. $E$ is convex and $D_n=E\times A$;
--   2. $x\mapsto L_nv(x,a)$ is convex for all $a\in A$.
--
--   Then $T_nv$ is convex on $E$. If moreover $A$ is a polytope and $a\mapsto L_nv(x,a)$ is convex for all $x\in E$, then there exists a **bang-bang maximizer** $f_n^*$ of $v$ at time $n$: a maximizer with $f_n^*(x)$ a vertex of $A$ for all $x\in E$.
--
--   The first clause drives Theorem 2.4.22; the second reduces the action search to the finitely many vertices.
--
--   **Formalization Note** "$A$ is a polytope" is $A=\operatorname{conv}V$ for a finite $V\subset\mathbb R^m$, and a vertex is an extreme point of $A$. A maximizer is a decision rule, so $f_n^*$ is measurable. Both clauses are stated.
--
--   Differences from the source:
--   - encoding: $E\subset\mathbb R^d$, $A\subset\mathbb R^m$ Borel spaces with the componentwise order (pp.29, 35) → subtypes of measurable sets `SE ⊆ Fin d → ℝ`, `SA ⊆ Fin m → ℝ` with the induced σ-algebra and the componentwise order; reason: a subset of $\mathbb R^d$ that is a Borel space is a Borel subset of $\mathbb R^d$; same instances
--   - encoding: $Q_n$ a stochastic kernel from $D_n$ to $E$ and $r_n:D_n\to\mathbb R$ (Definition 2.1.1) → the platform's `MarkovDecisionModel`, whose kernel and reward are given on all of $E\times A$; reason: only values on $D_n$ enter the statement; every model of the book extends (e.g. $Q_n=\delta_x$, $r_n=0$ off $D_n$)
--   - encoding: functions with values in $[-\infty,\infty)$ and $\int v\,dQ_n$ 'whenever the integral exists' → `EReal` values, `erealIntegral` = integral of $v^+$ minus integral of $v^-$; reason: for $v\in\mathbb B_b^+$ and $(x,a)\in D_n$ the positive part has finite integral, so this is the book's integral
--   - encoding: 'convex' / 'concave' for $[-\infty,\infty)$-valued functions (no numbered definition) → `ConvexOnVia` / `ConcaveOnVia`: the two-point inequality in `EReal` along the inclusion into $\mathbb R^d$ (or $\mathbb R^d\times\mathbb R^m$); reason: for functions without the value $+\infty$ this is convexity of the epigraph (hypograph); $-\infty$ allowed as in $\mathbb{IM}(E)$
--   - encoding: 'A is a polytope', 'vertex of A' → $A=\operatorname{conv}V$ with $V$ finite; extreme point of $A$; reason: the polytopes of $\mathbb R^m$ are the convex hulls of finite sets, and their vertices are their extreme points
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 2.4.21, p.37 (PDF p.52)

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_BauerleRiederMDP_ConvexModels_ConvexOnVia

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.ConvexModels

open MDPFinance.StructuredModels

/-- **Proposition 2.4.21** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Proposition 2.4.21, p.37, PDF p.52). Let `E ⊂ ℝ^d`, `A ⊂ ℝ^m` be Borel sets,
let the Markov Decision Model have upper bounding function `b`, let `v ∈ IB_b^+`, and
suppose
(i) `E` is convex and `D_n = E × A`;
(ii) `x ↦ L_n v(x,a)` is convex for all `a ∈ A`.
Then `T_n v` is convex on `E`. If moreover `A` is a polytope and `a ↦ L_n v(x,a)` is convex
for all `x ∈ E`, then there exists a bang-bang maximizer `f*_n` of `v` at time `n`, i.e. a
maximizer with `f*_n(x)` a vertex of `A` for all `x ∈ E`.

**Formalization Note.** `E`, `A` are subtypes of the Borel sets `SE ⊂ ℝ^d`, `SA ⊂ ℝ^m`;
convexity of `[−∞, ∞)`-valued functions is `ConvexOnVia` along the inclusion. "A is a
polytope" is `SA = convexHull ℝ V` for a finite set `V`, and a vertex of `A` is an extreme
point of `SA`. A maximizer is a decision rule, so the bang-bang maximizer is measurable. Both
clauses are stated; the second is an implication from the extra hypotheses. -/
theorem proposition_2_4_21 {d m N : ℕ} {SE : Set (Fin d → ℝ)} {SA : Set (Fin m → ℝ)}
    (hSE : MeasurableSet SE) (hSA : MeasurableSet SA)
    (M : MarkovDecisionModel SE SA N) (b : SE → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : SE → EReal) (hv : v ∈ IBbPlus b)
    (hE : Convex ℝ SE) (hD : M.D n = Set.univ)
    (hLx : ∀ a : SA, ConvexOnVia Subtype.val Set.univ (fun x => L M n v (x, a))) :
    ConvexOnVia Subtype.val Set.univ (T M n v) ∧
      ((∃ V : Finset (Fin m → ℝ), SA = convexHull ℝ (V : Set (Fin m → ℝ))) →
        (∀ x : SE, ConvexOnVia Subtype.val Set.univ (fun a => L M n v (x, a))) →
        ∃ f : SE → SA, IsMaximizer M n v f ∧ ∀ x, (f x : Fin m → ℝ) ∈ SA.extremePoints ℝ) := by sorry

end BauerleRiederMDP.ConvexModels
