-- Prove2me | Theorems.Thm_ConstrSOSP_Supplement_theorem_7_1
-- name    : ConstrSOSP.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:27:53.369897+00:00
-- url     : https://prove2.me/theorems/ebfa1c7b-10fd-4c5d-adeb-a8e818ee3b7a
-- title:
--   Theorem 7.1 — Sosp1 lies in PLS
-- statement:
--   **Theorem 7.1.** Sosp1 lies in PLS.
--
--   Here Sosp1 is the total white-box problem of Definition 4.6: the input is precision parameters $\epsilon_G,\epsilon_H>0$, a bounded non-empty polytope $\mathcal X=\{x\in\mathbb R^d: Ax\le B\}$ in any dimension $d$, polynomial-time Turing machines for $f$, $\nabla f$, $\nabla^2 f$, and Lipschitz constants $L,L_1,L_2>0$; an answer is an $(\epsilon_G,\epsilon_H)$-SOSP1 $x^*\in\mathcal X$,
--
--   $$\|g_\pi(x^*)\|\le\epsilon_G,\qquad y^\top\nabla^2 f(x^*)\,y\ge-\epsilon_H\ \text{ for all unit } y \text{ with } A'(x^*)y=0,$$
--
--   or a pair $x,y\in\mathcal X$ witnessing that $f$, $\nabla f$ or $\nabla^2 f$ is not Lipschitz with the given constants, or that $\nabla f$ or $\nabla^2 f$ violates the first- or second-order Taylor bound.
--
--   The theorem says that, for every fixed exponent $K$ of the machines' running time, (1) a candidate answer can be checked in polynomial time and (2) Sosp1 reduces in polynomial time to LocalOpt. Together with Corollary 5.6 it makes Sosp1 PLS-complete.
--
--   **Formalization Note** PLS membership is `InPLS`; the machines are run for $T\cdot(|w|+1)^K$ steps with $T$ written in unary in the instance.
--
--   Differences from the source:
--   - reading: "lies in PLS" = TFNP problem that reduces to LocalOpt (p.17) → InPLS: a polynomial-time checker that decides the answer relation on every valid instance, and a polynomial-time search reduction (SearchReduces) to LocalOpt; reason: the paper's own definition of PLS; the checker runs in time polynomial in |s|+|t|, with no bound on the answer length, because the paper's answers are rational points of arbitrary bit length
--   - reading: "Turing machine for f, ∇f, ∇²f" running in polynomial time (p.17) → machine codes run for T·(|w|+1)^K steps, T in unary in the instance; validity asks that they return well-formed rational values at every rational point of X; membership is stated for every K; reason: the paper leaves the time bound implicit; a fixed exponent with a unary clock is the base mission's reading, and every fixed K is the strongest form
--   - reading: ‖∇²f(x) − ∇²f(y)‖ > L₂‖x − y‖ with ‖·‖ "the Euclidean norm ‖·‖₂" (p.18) → operator (spectral) norm, HighDimProb.QuadraticForms.opNorm; reason: the matrix norm induced by ‖·‖₂; it is never larger than the Frobenius norm, so this gives the smaller set of violation answers and the harder membership claim
--   - encoding: real data ϵG, ϵH, A, B, L, L₁, L₂ and points x* ∈ X → rationals written in binary; answer points are rational; reason: white-box instances and answers are finite strings; the paper's machines take and return rationals (p.17)
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Theorem 7.1, p.60 (Sosp1: Definition 4.6, pp.19–20; PLS: §4.1, p.17)

import Mathlib
import Definitions.Def_ConstrSOSP_Supplement_Sosp1Gen
import Definitions.Def_ConstrSOSP_Supplement_InPLS

namespace ConstrSOSP.Supplement

/-- **Theorem 7.1** (Kontogiannis, Panageas & Pollatos, *The Computational Complexity of Avoiding
Strict Saddle Points in Constrained Optimization*, arXiv:2604.02285, version of 2 November 2026,
p.60): "Sosp1 lies in PLS."

For every clock exponent `K`, the total white-box problem Sosp1 of Definition 4.6 (every dimension,
every bounded non-empty rational polytope `{Ax ≤ B}`, arbitrary rational `ϵG, ϵH, L, L₁, L₂ > 0`,
answers: an `(ϵG, ϵH)`-SOSP1 or a regularity violation) is in PLS: its answers are checkable in
polynomial time and it reduces in polynomial time to LocalOpt.

**Formalization Note** The white-box functions are machine codes run for `T · (|w| + 1)^K` steps,
`T` in unary in the instance; membership is claimed for every fixed `K`. -/
theorem theorem_7_1 : ∀ K : ℕ, InPLS (Sosp1Gen K) := by sorry

end ConstrSOSP.Supplement
