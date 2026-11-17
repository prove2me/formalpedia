-- Prove2me | Theorems.Thm_ConstrSOSP_Supplement_theorem_7_9
-- name    : ConstrSOSP.Supplement.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:29:02.711342+00:00
-- url     : https://prove2.me/theorems/b4c821df-437c-450b-9222-7dfd14c94057
-- title:
--   Theorem 7.9 — Fixed-Dimensions-Sosp2 belongs to PLS for every fixed $d_0\ge1$
-- statement:
--   **Theorem 7.9.** For every fixed integer $d_0\ge1$, independent of the input, Fixed-Dimensions-Sosp2 belongs to PLS.
--
--   Here Fixed-Dimensions-Sosp2 is the total white-box problem of Definition 4.8 in dimension $d_0$: the input is precision parameters $\epsilon_G,\epsilon_H>0$, a bounded non-empty polytope $\mathcal X=\{x\in\mathbb R^{d_0}: Ax\le B\}$, polynomial-time Turing machines for $f$, $\nabla f$, $\nabla^2 f$, and Lipschitz constants $L,L_1,L_2>0$; an answer is an $(\epsilon_G,\epsilon_H)$-SOSP2 $x^*\in\mathcal X$, that is, for every $s$ with $x^*+s\in\mathcal X$ and $\|s\|\le1$,
--
--   $$\nabla f(x^*)^\top s\ge-\epsilon_G,\qquad \nabla f(x^*)^\top s\le0\ \Longrightarrow\ s^\top\nabla^2 f(x^*)\,s\ge-\epsilon_H,$$
--
--   or a regularity violation as in Sosp1.
--
--   The theorem says that for every $d_0\ge1$ and every fixed exponent $K$ of the machines' running time, candidate answers are checkable in polynomial time and the problem reduces in polynomial time to LocalOpt. Checking an SOSP2 is coNP-hard in high dimension, which is why the dimension is fixed.
--
--   **Formalization Note** $d_0$ and $K$ are parameters of the problem; the polynomial bounds may depend on both.
--
--   Differences from the source:
--   - reading: "lies in PLS" = TFNP problem that reduces to LocalOpt (p.17) → InPLS: a polynomial-time checker that decides the answer relation on every valid instance, and a polynomial-time search reduction (SearchReduces) to LocalOpt; reason: the paper's own definition of PLS; the checker runs in time polynomial in |s|+|t|, with no bound on the answer length, because the paper's answers are rational points of arbitrary bit length
--   - reading: "Turing machine for f, ∇f, ∇²f" running in polynomial time (p.17) → machine codes run for T·(|w|+1)^K steps, T in unary in the instance; validity asks that they return well-formed rational values at every rational point of X; membership is stated for every K; reason: the paper leaves the time bound implicit; a fixed exponent with a unary clock is the base mission's reading, and every fixed K is the strongest form
--   - reading: ‖∇²f(x) − ∇²f(y)‖ > L₂‖x − y‖ with ‖·‖ "the Euclidean norm ‖·‖₂" (p.18) → operator (spectral) norm, HighDimProb.QuadraticForms.opNorm; reason: the matrix norm induced by ‖·‖₂; it is never larger than the Frobenius norm, so this gives the smaller set of violation answers and the harder membership claim
--   - encoding: real data ϵG, ϵH, A, B, L, L₁, L₂ and points x* ∈ X → rationals written in binary; answer points are rational; reason: white-box instances and answers are finite strings; the paper's machines take and return rationals (p.17)
--   - reading: Definition 4.8: "Fix an integer d0 ≥ 2"; Theorem 7.9: "For every fixed integer d0 ≥ 1" → FixedDimSosp2 d0 K defined for every d0; the theorem quantifies over every d0 ≥ 1; reason: the theorem's own range; for d0 ≥ 2 it is exactly Definition 4.8, and d0 = 1 is the same definition read in dimension 1
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Theorem 7.9, p.71 (Fixed-Dimensions-Sosp2: Definition 4.8, pp.20–21; PLS: §4.1, p.17)

import Mathlib
import Definitions.Def_ConstrSOSP_Supplement_FixedDimSosp2
import Definitions.Def_ConstrSOSP_Supplement_InPLS

namespace ConstrSOSP.Supplement

/-- **Theorem 7.9** (Kontogiannis, Panageas & Pollatos, *The Computational Complexity of Avoiding
Strict Saddle Points in Constrained Optimization*, arXiv:2604.02285, version of 2 November 2026,
p.71): "For every fixed integer d0 ≥ 1, independent of the input, Fixed-Dimensions-Sosp2 belongs to
PLS."

For every `d₀ ≥ 1` and every clock exponent `K`, the total white-box problem Fixed-Dimensions-Sosp2
of Definition 4.8 in dimension `d₀` (every bounded non-empty rational polytope in `ℝ^{d₀}`,
arbitrary rational `ϵG, ϵH, L, L₁, L₂ > 0`, answers: an `(ϵG, ϵH)`-SOSP2 or a regularity violation)
is in PLS.

**Formalization Note** `d₀` and `K` are parameters of the problem, fixed before the input; the
polynomial bounds of the checker and of the reduction may depend on both. -/
theorem theorem_7_9 : ∀ d0 : ℕ, 1 ≤ d0 → ∀ K : ℕ, InPLS (FixedDimSosp2 d0 K) := by sorry

end ConstrSOSP.Supplement
