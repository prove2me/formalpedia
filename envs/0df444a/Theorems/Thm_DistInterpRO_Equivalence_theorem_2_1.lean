-- Prove2me | Theorems.Thm_DistInterpRO_Equivalence_theorem_2_1
-- name    : DistInterpRO.Equivalence.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:45:54.535719+00:00
-- url     : https://prove2.me/theorems/2eef91b1-9523-437d-adc9-d5222069e0d7
-- title:
--   Theorem 2.1 — Robust optimization over $n$ overlapping sets in $\mathbb R^m$ equals a worst-case expectation over $\mathcal P_n$
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ be a measurable function, let $c_1,\dots,c_n>0$ with $\sum_{i=1}^n c_i=1$, and let $\mathcal Z_1,\dots,\mathcal Z_n\subseteq\mathbb R^m$ be nonempty Borel sets (they may overlap, or even coincide). Let
--   $$\mathcal P_n=\Big\{\mu\in\mathcal P\ \Big|\ \forall S\subseteq[1:n]:\ \mu\Big(\bigcup_{i\in S}\mathcal Z_i\Big)\ge\sum_{i\in S}c_i\Big\},$$
--   where $\mathcal P$ is the set of Borel probability measures on $\mathbb R^m$. Then
--   $$\sum_{i=1}^n\Big[c_i\inf_{x_i\in\mathcal Z_i}f(x_i)\Big]=\inf_{\mu\in\mathcal P_n}\int_{\mathbb R^m}f(x)\,d\mu(x),$$
--   as an identity in $[-\infty,+\infty]$.
--
--   The left side is the inner (worst-case) problem of robust optimization with $n$ uncertain parameters in the same space; the right side is the inner problem of a distributionally robust stochastic program. The theorem identifies the two for every fixed decision, and is the basis of the consistency and shrinkage results of the paper.
--
--   **Formalization Note** (1) The paper allows $f$ to take the value $-\infty$; here $f$ is real-valued. The excluded case, $f=-\infty$ somewhere in $\bigcup_i\mathcal Z_i$, is the one the proof disposes of in its first sentence (both sides equal $-\infty$). (2) Both sides are computed in the extended reals `EReal`: the infima $\inf_{\mathcal Z_i}f$ may be $-\infty$, and $\int f\,d\mu$ is the extended expectation $\int f^+d\mu-\int f^-d\mu$ (with $\infty-\infty=-\infty$), never a Bochner integral, so an infinite integral is not replaced by $0$. No boundedness hypothesis is imposed: when every $\inf_{\mathcal Z_i}f$ is finite, $f$ is bounded below on $\bigcup_i\mathcal Z_i$, which carries every $\mu\in\mathcal P_n$, so the negative part is finite; when some infimum is $-\infty$ both sides are $-\infty$. (3) Indices are `Fin n`; the constraint is imposed for every `S : Finset (Fin n)`, including $\emptyset$ and $[1:n]$.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), pp. 96–97, Theorem 2.1, Eq. (4)

import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem theorem_2_1 {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i)) :
    (∑ i, ((c i : ℝ) : EReal) * ⨅ x ∈ Z i, ((f x : ℝ) : EReal)) =
      ⨅ μ ∈ distSet c Z, expect μ f := by sorry

end DistInterpRO.Equivalence
