-- Prove2me | Theorems.Thm_DistInterpRO_Equivalence_carried_by_union
-- name    : DistInterpRO.Equivalence.carried_by_union
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:44:26.257967+00:00
-- url     : https://prove2.me/theorems/0cc5a8b2-57ae-46a5-bf8d-84cf0587dba0
-- title:
--   Every $\mu\in\mathcal P_n$ is carried by $\mathcal Z_N$, so $\int_{\mathbb R^m} f\,d\mu=\int_{\mathcal Z_N} f\,d\mu$
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ be measurable, let $c_1,\dots,c_n>0$ with $\sum_{i=1}^n c_i=1$, and let $\mathcal Z_1,\dots,\mathcal Z_n\subseteq\mathbb R^m$ be nonempty Borel sets, with $\mathcal Z_N=\bigcup_{i=1}^n\mathcal Z_i$. For every $\mu$ in the distribution set $\mathcal P_n$ of Theorem 2.1,
--   $$\mu\big(\mathbb R^m\setminus\mathcal Z_N\big)=0\qquad\text{and}\qquad \int_{\mathbb R^m}f\,d\mu=\int_{\mathcal Z_N}f\,d\mu,$$
--   where both integrals are extended expectations $\int f^+-\int f^-\in[-\infty,+\infty]$.
--
--   This is the observation in the proof of Theorem 2.1 that lets the dual problem be posed on $\mathcal Z_N$ only: the constraint for $S=[1:n]$ forces $\mu$ to put all its mass on $\mathcal Z_N$.
--
--   **Formalization Note** The integral over $\mathcal Z_N$ is the extended expectation with respect to the restriction `μ.restrict (⋃ i, Z i)`. The first conjunct is the content; the second is the identity as printed.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 97, proof of Theorem 2.1, sentence before the dual problem

import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem carried_by_union {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (μ : Measure (Fin m → ℝ)) (hμ : μ ∈ distSet c Z) :
    μ (⋃ i, Z i)ᶜ = 0 ∧ expect μ f = expect (μ.restrict (⋃ i, Z i)) f := by sorry

end DistInterpRO.Equivalence
