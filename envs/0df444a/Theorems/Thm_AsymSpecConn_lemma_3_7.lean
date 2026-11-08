-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_3_7
-- name    : AsymSpecConn.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:18.098199+00:00
-- url     : https://prove2.me/theorems/a546304d-8bb2-4ad9-9184-f6553db15a2e
-- title:
--   Lemma 3.7 — few translates of a proper subspace intersect in $0$
-- statement:
--   Let $F$ be any field, let a finite group $G$ act irreducibly on a nonzero finite-dimensional $F$-vector space $V$, and let $W\subsetneq V$ be a proper subspace. Then there is $q\in\mathbb N$ with
--   $$q\le\frac{\dim V}{\dim V-\dim W}\,(1+\ln\dim V)$$
--   and $g_1,\dots,g_q\in G$ such that $g_1W\cap\dots\cap g_qW=0$.
--
--   This bound enters the reverse monotonicity estimate for spectral points.
--
--   **Formalization Note** $\ln$ is the natural logarithm; $\dim V\ge1$, so its argument is positive. Finite-dimensionality is the source's standing convention (p.12).
--
--   Differences from the source: none.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.7, p.24

import Mathlib

set_option autoImplicit false

namespace AsymSpecConn

/-- **Lemma 3.7** (p.24 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Let F be any field, let a finite group G
act irreducibly on a nonzero F-vector space V, and let W ⊊ V be a proper subspace. Then there is
q ∈ N with q ≤ (dim V / (dim V − dim W)) (1 + ln dim V) and g1, …, gq ∈ G such that
g1W ∩ ⋯ ∩ gqW = 0."

**Formalization Note** `ln` is the natural logarithm `Real.log`. `g_jW` is `W.map (ρ (g j))`;
the intersection is `⨅ j` (for `q = 0` it would be `V ≠ 0`). `V` is finite-dimensional. -/
theorem lemma_3_7 (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G] (V : Type*)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (ρ : Representation F G V)
    (hρ : ρ.IsIrreducible) (W : Submodule F V) (hW : W ≠ ⊤) :
    ∃ (q : ℕ) (g : Fin q → G),
      (q : ℝ) ≤ (Module.finrank F V : ℝ) / ((Module.finrank F V : ℝ) - (Module.finrank F W : ℝ)) *
        (1 + Real.log (Module.finrank F V : ℝ)) ∧
      (⨅ j, W.map (ρ (g j))) = ⊥ := by sorry

end AsymSpecConn
