-- Prove2me | Theorems.Thm_BauerleRiederMDP_ConvexModels_theorem_2_4_19
-- name    : BauerleRiederMDP.ConvexModels.theorem_2_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:23:47.329814+00:00
-- url     : https://prove2.me/theorems/00de12f3-8ed2-4105-a107-9851402596c9
-- title:
--   Theorem 2.4.19 — concave functions in $\mathbb B_b^+$ satisfy the Structure Assumption
-- statement:
--   Throughout, $E\subset\mathbb R^d$ and $A\subset\mathbb R^m$ are Borel sets carrying the componentwise order, and $(E,A,D_n,Q_n,r_n,g_N)$ is a Markov Decision Model with planning horizon $N$: $D_n\subset E\times A$ are the admissible state–action pairs, $Q_n(\cdot\mid x,a)$ the transition kernels, $r_n$ the one-stage rewards and $g_N$ the terminal reward. The model has an **upper bounding function** $b\ge 0$ (Definition 2.4.1): $r_n^+\le c_r b$, $g_N^+\le c_g b$ and $\int b\,dQ_n(\cdot\mid x,a)\le\alpha_b b(x)$ on $D_n$. Write
--   $$
--   \mathbb B_b^+=\{v:E\to[-\infty,\infty)\text{ measurable}\mid v^+\le c\,b\text{ for some }c\ge 0\},\qquad L_nv(x,a)=r_n(x,a)+\int v(x')\,Q_n(dx'\mid x,a),\qquad T_nv(x)=\sup_{a\in D_n(x)}L_nv(x,a).
--   $$
--   A **maximizer** of $v$ at time $n$ is a decision rule $f\in F_n$ (a measurable $f$ with $f(x)\in D_n(x)$) with $L_nv(x,f(x))=T_nv(x)$ for all $x$.
--
--   Suppose that for all $n=0,1,\dots,N-1$:
--
--   1. $D_n$ is convex in $E\times A$;
--   2. $(x,a)\mapsto\int v(x')\,Q_n(dx'\mid x,a)$ is concave on $D_n$ for all concave $v\in\mathbb B_b^+$;
--   3. $(x,a)\mapsto r_n(x,a)$ is concave on $D_n$;
--   4. $g_N$ is concave on $E$;
--   5. for all concave $v\in\mathbb B_b^+$ there exists a maximizer $f_n\in\Delta_n$ of $v$, where $\Delta_n\subset F_n$.
--
--   Then the sets
--   $$
--   \mathbb{IM}_n:=\{v\in\mathbb B_b^+\mid v\text{ is concave}\}
--   $$
--   and $\Delta_n$ satisfy the Structure Assumption $(\mathrm{SA}_N)$. (SAN) for sets $\mathbb{IM}_n$, $\Delta_n$ means: $\mathbb{IM}_n$ consists of measurable $[-\infty,\infty)$-valued functions, $\Delta_n\subset F_n$, $g_N\in\mathbb{IM}_N$, and for every $n<N$ and $v\in\mathbb{IM}_{n+1}$ the operator $T_nv$ is well defined, lies in $\mathbb{IM}_n$, and $v$ has a maximizer in $\Delta_n$.
--
--   With Theorem 2.3.8 this gives concave value functions, the case used for utility maximization in Chapter 4.
--
--   **Formalization Note** The book numbers conditions 4 and 5 both "(iv)"; both are hypotheses.
--
--   Differences from the source:
--   - encoding: $E\subset\mathbb R^d$, $A\subset\mathbb R^m$ Borel spaces with the componentwise order (pp.29, 35) → subtypes of measurable sets `SE ⊆ Fin d → ℝ`, `SA ⊆ Fin m → ℝ` with the induced σ-algebra and the componentwise order; reason: a subset of $\mathbb R^d$ that is a Borel space is a Borel subset of $\mathbb R^d$; same instances
--   - encoding: $Q_n$ a stochastic kernel from $D_n$ to $E$ and $r_n:D_n\to\mathbb R$ (Definition 2.1.1) → the platform's `MarkovDecisionModel`, whose kernel and reward are given on all of $E\times A$; reason: only values on $D_n$ enter the statement; every model of the book extends (e.g. $Q_n=\delta_x$, $r_n=0$ off $D_n$)
--   - encoding: functions with values in $[-\infty,\infty)$ and $\int v\,dQ_n$ 'whenever the integral exists' → `EReal` values, `erealIntegral` = integral of $v^+$ minus integral of $v^-$; reason: for $v\in\mathbb B_b^+$ and $(x,a)\in D_n$ the positive part has finite integral, so this is the book's integral
--   - encoding: (SAN) (ii) '$T_nv$ is well-defined' → every integral $\int v\,dQ_n(\cdot|x,a)$, $(x,a)\in D_n$, exists (finite positive or negative part); reason: Definition 2.3.1 a) defines $L_nv$ 'whenever the integral exists'
--   - encoding: 'convex' / 'concave' for $[-\infty,\infty)$-valued functions (no numbered definition) → `ConvexOnVia` / `ConcaveOnVia`: the two-point inequality in `EReal` along the inclusion into $\mathbb R^d$ (or $\mathbb R^d\times\mathbb R^m$); reason: for functions without the value $+\infty$ this is convexity of the epigraph (hypograph); $-\infty$ allowed as in $\mathbb{IM}(E)$
--   - reading: $\Delta_n$ (unqualified in the theorem) → hypothesis $\Delta_n\subseteq F_n$ (decision rules); reason: (SAN), p.23, takes $\Delta_n\subset F_n$; without it the conclusion fails for a $\Delta_n$ containing a non-measurable map
--   - reading: (ii), (iii): '(x,a) ↦ … is concave' → concave on $D_n$; reason: $Q_n$ and $r_n$ are defined on $D_n$, which is convex by (i)
--   - reading: two conditions numbered '(iv)' → both are hypotheses (`hg`, `hmax`); reason: typographical; the second is the book's (v) (paper.md reading 1)
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.4.19, p.37 (PDF p.52); standing assumptions p.29 (PDF p.44)

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_BauerleRiederMDP_ConvexModels_StructureAssumption
import Definitions.Def_BauerleRiederMDP_ConvexModels_ConcaveOnVia

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.ConvexModels

open MDPFinance.StructuredModels

/-- **Theorem 2.4.19** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Theorem 2.4.19, p.37, PDF p.52). Let `E ⊂ ℝ^d`, `A ⊂ ℝ^m` be Borel sets and
suppose a Markov Decision Model with upper bounding function `b` is given such that for all
`n = 0, 1, …, N − 1`:
(i) `D_n` is convex in `E × A`;
(ii) `(x,a) ↦ ∫ v(x′) Q_n(dx′|x,a)` is concave (on `D_n`) for all concave `v ∈ IB_b^+`;
(iii) `(x,a) ↦ r_n(x,a)` is concave (on `D_n`);
(iv) `g_N` is concave on `E`;
(v) for all concave `v ∈ IB_b^+` there exists a maximizer `f_n ∈ Δ_n` of `v`.
Then `IM_n := {v ∈ IB_b^+ | v concave}` and `Δ_n` satisfy the Structure Assumption (SAN).

**Formalization Note.** The book numbers the last two conditions "(iv)"; both are
hypotheses. `E`, `A` are subtypes of the Borel sets `SE ⊂ ℝ^d`, `SA ⊂ ℝ^m`; convexity of
`D_n` is convexity of its image in `ℝ^d × ℝ^m`, and concavity of the `[−∞, ∞)`-valued
functions is `ConcaveOnVia`. Because `r_n` and `Q_n` are defined on `D_n`, (ii) and (iii)
are concavity on `D_n`. `Δ_n ⊂ F_n` is the book's standing meaning of `Δ_n` in (SAN), p.23. -/
theorem theorem_2_4_19 {d m N : ℕ} {SE : Set (Fin d → ℝ)} {SA : Set (Fin m → ℝ)}
    (hSE : MeasurableSet SE) (hSA : MeasurableSet SA)
    (M : MarkovDecisionModel SE SA N) (b : SE → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (Δ : ℕ → Set (SE → SA)) (hΔ : ∀ n < N, Δ n ⊆ {f | IsDecisionRule M n f})
    (hD : ∀ n < N, Convex ℝ (Prod.map Subtype.val Subtype.val '' M.D n))
    (hQ : ∀ n < N, ∀ v ∈ IBbPlus b, ConcaveOnVia Subtype.val Set.univ v →
      ConcaveOnVia (Prod.map Subtype.val Subtype.val) (M.D n)
        (fun xa => erealIntegral (M.Q n xa) v))
    (hr : ∀ n < N, ConcaveOnVia (Prod.map Subtype.val Subtype.val) (M.D n)
      (fun xa => (M.r n xa : EReal)))
    (hg : ConcaveOnVia Subtype.val Set.univ (fun x => (M.g x : EReal)))
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, ConcaveOnVia Subtype.val Set.univ v →
      ∃ f ∈ Δ n, IsMaximizer M n v f) :
    StructureAssumption M (fun _ => {v ∈ IBbPlus b | ConcaveOnVia Subtype.val Set.univ v}) Δ := by sorry

end BauerleRiederMDP.ConvexModels
