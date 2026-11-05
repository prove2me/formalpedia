-- Prove2me | Theorems.Thm_BauerleRiederMDP_ConvexModels_proposition_2_4_16
-- name    : BauerleRiederMDP.ConvexModels.proposition_2_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:23:40.840022+00:00
-- url     : https://prove2.me/theorems/b319ef35-f755-4255-a67a-70a0b242fcc5
-- title:
--   Proposition 2.4.16 — a largest maximizer of a supermodular $L_nv$ is weakly increasing
-- statement:
--   Throughout, $E\subset\mathbb R^d$ and $A\subset\mathbb R^m$ are Borel sets carrying the componentwise order, and $(E,A,D_n,Q_n,r_n,g_N)$ is a Markov Decision Model with planning horizon $N$: $D_n\subset E\times A$ are the admissible state–action pairs, $Q_n(\cdot\mid x,a)$ the transition kernels, $r_n$ the one-stage rewards and $g_N$ the terminal reward. The model has an **upper bounding function** $b\ge 0$ (Definition 2.4.1): $r_n^+\le c_r b$, $g_N^+\le c_g b$ and $\int b\,dQ_n(\cdot\mid x,a)\le\alpha_b b(x)$ on $D_n$. Write
--   $$
--   \mathbb B_b^+=\{v:E\to[-\infty,\infty)\text{ measurable}\mid v^+\le c\,b\text{ for some }c\ge 0\},\qquad L_nv(x,a)=r_n(x,a)+\int v(x')\,Q_n(dx'\mid x,a),\qquad T_nv(x)=\sup_{a\in D_n(x)}L_nv(x,a).
--   $$
--   A **maximizer** of $v$ at time $n$ is a decision rule $f\in F_n$ (a measurable $f$ with $f(x)\in D_n(x)$) with $L_nv(x,f(x))=T_nv(x)$ for all $x$.
--
--   Let $v\in\mathbb B_b^+$, fix $n<N$ and put $D_n^*(x):=\{a\in D_n(x)\mid L_nv(x,a)=T_nv(x)\}$. Suppose
--
--   1. $D_n$ is **completely monotone**: for $(x,a'),(x',a)\in D_n$ with $x\le x'$ and $a\le a'$ also $(x,a),(x',a')\in D_n$;
--   2. $L_nv$ is supermodular on $D_n$ (in particular real-valued there);
--   3. $f_n^*$ is a **largest maximizer** of $v$: a maximizer of $v$ at time $n$ such that for all $x\in E$, $f_n^*(x)\ge a$ for every $a\in D_n^*(x)$ comparable with $f_n^*(x)$.
--
--   Then $f_n^*$ is weakly increasing:
--   $$
--   x\le x'\ \text{ and }\ f_n^*(x),f_n^*(x')\text{ comparable}\ \Longrightarrow\ f_n^*(x)\le f_n^*(x').
--   $$
--   Together with Theorem 2.4.14 this lets $\Delta_n$ be the weakly increasing decision rules.
--
--   **Formalization Note** Complete monotonicity is the platform's `CompletelyMonotone`. Supermodularity on $D_n$ requires the inequality for points of $D_n$ whose componentwise minimum and maximum lie in $D_n$.
--
--   Differences from the source:
--   - encoding: $E\subset\mathbb R^d$, $A\subset\mathbb R^m$ Borel spaces with the componentwise order (pp.29, 35) → subtypes of measurable sets `SE ⊆ Fin d → ℝ`, `SA ⊆ Fin m → ℝ` with the induced σ-algebra and the componentwise order; reason: a subset of $\mathbb R^d$ that is a Borel space is a Borel subset of $\mathbb R^d$; same instances
--   - encoding: $Q_n$ a stochastic kernel from $D_n$ to $E$ and $r_n:D_n\to\mathbb R$ (Definition 2.1.1) → the platform's `MarkovDecisionModel`, whose kernel and reward are given on all of $E\times A$; reason: only values on $D_n$ enter the statement; every model of the book extends (e.g. $Q_n=\delta_x$, $r_n=0$ off $D_n$)
--   - encoding: functions with values in $[-\infty,\infty)$ and $\int v\,dQ_n$ 'whenever the integral exists' → `EReal` values, `erealIntegral` = integral of $v^+$ minus integral of $v^-$; reason: for $v\in\mathbb B_b^+$ and $(x,a)\in D_n$ the positive part has finite integral, so this is the book's integral
--   - reading: '$L_nv$ is supermodular on $D_n$' for an $L_nv$ that may take the value $-\infty$ → $L_nv$ real-valued on $D_n$ and $L_nv(p)+L_nv(q)\le L_nv(p\wedge q)+L_nv(p\vee q)$ for $p,q,p\wedge q,p\vee q\in D_n$; reason: Definition A.3.1 is for real-valued functions; with $-\infty$ allowed and $-\infty+c=-\infty$ the proposition is false (E = {0,1,2}, A = {0,1}: $L_nv(0,\cdot)=-\infty$, $L_nv(1,0)=0$, $L_nv(1,1)=-1$ gives $f^*(0)=1>f^*(1)=0$)
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 2.4.16, pp.35–36 (PDF pp.50–51); Definition 2.4.15, p.35; Definition A.3.1, p.353 (PDF p.359)

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_CompletelyMonotone
import Definitions.Def_BauerleRiederMDP_ConvexModels_SupermodularOnVia

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.ConvexModels

open MDPFinance.StructuredModels

/-- **Proposition 2.4.16** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Proposition 2.4.16, pp.35–36, PDF pp.50–51). Let `E ⊂ ℝ^d`, `A ⊂ ℝ^m` be
Borel sets with the componentwise order, let the Markov Decision Model have upper bounding
function `b`, let `v ∈ IB_b^+` and write `D*_n(x) := {a ∈ D_n(x) | L_n v(x,a) = T_n v(x)}`.
Suppose
(i) `D_n` is completely monotone (Definition 2.4.15, p.35);
(ii) `L_n v` is supermodular on `D_n` (Definition A.3.1, p.353);
(iii) `f*_n` is a largest maximizer of `v`: a maximizer of `v` at time `n` such that for all
`x ∈ E`, `f*_n(x) ≥ a` for all `a ∈ D*_n(x)` comparable with `f*_n(x)`.
Then `f*_n` is weakly increasing: `x ≤ x′` implies `f*_n(x) ≤ f*_n(x′)` whenever `f*_n(x)`
and `f*_n(x′)` are comparable.

**Formalization Note.** `E`, `A` are subtypes of the Borel sets `SE ⊂ ℝ^d`, `SA ⊂ ℝ^m` with
the componentwise order; complete monotonicity is the platform's `CompletelyMonotone`
(Definition 2.4.15 verbatim). Supermodularity of `L_n v` on `D_n` is `SupermodularOnVia`
with `D_n ⊂ ℝ^d × ℝ^m`: by Definition A.3.1 the function is real-valued on `D_n`, and the
inequality is required for the pairs of `D_n` whose componentwise minimum and maximum lie in
`D_n`. -/
theorem proposition_2_4_16 {d m N : ℕ} {SE : Set (Fin d → ℝ)} {SA : Set (Fin m → ℝ)}
    (hSE : MeasurableSet SE) (hSA : MeasurableSet SA)
    (M : MarkovDecisionModel SE SA N) (b : SE → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : SE → EReal) (hv : v ∈ IBbPlus b)
    (hCM : CompletelyMonotone (M.D n))
    (hSM : SupermodularOnVia (Prod.map Subtype.val Subtype.val) (M.D n) (L M n v))
    (f : SE → SA) (hf : IsMaximizer M n v f)
    (hlargest : ∀ x : SE, ∀ a ∈ M.Dx n x, L M n v (x, a) = T M n v x →
      (a ≤ f x ∨ f x ≤ a) → a ≤ f x) :
    ∀ x x' : SE, x ≤ x' → (f x ≤ f x' ∨ f x' ≤ f x) → f x ≤ f x' := by sorry

end BauerleRiederMDP.ConvexModels
