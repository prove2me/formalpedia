-- Prove2me | Theorems.Thm_ConstrSOSP_theorem_5_1
-- name    : ConstrSOSP.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:08:42.095635+00:00
-- url     : https://prove2.me/theorems/463fccb7-3cb1-4558-ae8e-df023ee03096
-- title:
--   Theorem 5.1: finding an approximate SOSP, SOSP1 or SOSP2 on $[0,1]^2$ is PLS-hard
-- statement:
--   Consider white-box instances on the unit square $\mathcal X=[0,1]^2$: precisions $\epsilon_G,\epsilon_H$ and polynomial-time Turing machines for $f$, $\nabla f$, $\nabla^2f$. Restrict to the instances where
--
--   1. $\epsilon_G=\epsilon$ and $\epsilon_H=\sqrt\epsilon$ for some $\epsilon>0$;
--   2. all regularity promises hold with $L=L_1=L_2=1$ (Lipschitz, smoothness, Hessian-Lipschitz and the two Taylor conditions);
--   3. every $\epsilon$-approximate KKT point (proximal gradient with smoothness constant $1$) lies in $[1/12,11/12]^2$.
--
--   **Theorem.** Each of the following search problems on these instances is PLS-hard:
--
--   1. **Interior-Sosp**: find $x^*\in(0,1)^2$ with $\|\nabla f(x^*)\|\le\epsilon$ and $\nabla^2f(x^*)\succeq-\sqrt\epsilon\,I$;
--   2. **Sosp1**: find an $(\epsilon,\sqrt\epsilon)$-SOSP1 $x^*\in[0,1]^2$;
--   3. **Sosp2**: find an $(\epsilon,\sqrt\epsilon)$-SOSP2 $x^*\in[0,1]^2$.
--
--   Formally: there is $K_0$ such that for every clock exponent $K\ge K_0$, every search problem that reduces in polynomial time to LocalOpt also reduces in polynomial time to each of the three problems.
--
--   Approximate second-order stationary points of smooth nonconvex functions on a polytope are therefore as hard to find as local optima of general local-search problems, already in dimension two with unit regularity constants and when no approximate KKT point is near the boundary.
--
--   **Formalization Note** PLS is the class of TFNP problems reducing to LocalOpt (p.17), so the reduction closure is PLS-hardness. White-box functions are machine codes run with the clock $T\cdot(|w|+1)^K$, $T$ in unary in the instance and $K$ fixed by the problem.
--
--   Differences from the source:
--   - generalization: "PLS-hard" → every search problem that reduces in polynomial time to LocalOpt also reduces to each target problem; reason: PLS is the class of TFNP problems that reduce to LocalOpt (p.17); here the source problem need not be in TFNP, so the statement covers PLS and specializes to it
--   - reading: "Turing machine for f" running in polynomial time (p.17) → a machine code run for T·(|w|+1)^K steps, with T written in unary in the instance and the exponent K fixed by the problem; the statement holds for every K ≥ K₀; reason: the paper leaves the time bound implicit; an instance-chosen exponent or a binary clock would let a reduction hide exponential work, so the fixed-exponent unary clock is the faithful reading
--   - reading: ‖∇²f(x) − ∇²f(y)‖ with an unspecified matrix norm (Definitions 4.6, 4.8, 4.10) → Frobenius norm; reason: the norm of the proof of Lemma 5.4 ("Throughout the proof, matrix norms are Frobenius norms", p.49); it bounds the spectral norm, so the promise is the stronger one
--   - encoding: white-box functions given by polynomial-time Turing machines (p.17) → machine codes of Cook Turing machines, evaluated on binary codes of rational points (encRatVec), outputs as binary rationals (encRat, encRatVec, encRatMatrix); reason: p.17 fixes rational white-box semantics; Lean convention; same instances
--   - encoding: promises and answers at points of [0, 1]² → promises quantified over rational points; answers are rational points; reason: p.17: f(x), ∇f(x), ∇²f(x) at rational inputs denote the machines' rational outputs and the Lipschitz and Taylor conditions refer to these maps
--   - encoding: instances list A, B, L, L₁, L₂ and accept violation certificates (Definitions 4.6, 4.8, 4.10) → A = [I; −I], B = (1, 1, 0, 0), L = L₁ = L₂ = 1 are fixed and not written; violation certificates are not answers; reason: Theorem 5.1 fixes these data; on a valid instance the promises exclude every Lipschitz and Taylor violation and the KKT margin excludes a boundary SOSP1, so the answer sets coincide
--   - encoding: the SOSP2 consequence proved at accuracy (η, √η) with η = ρ⁴ϵ and renamed (p.57: "Renaming the target accuracy η as ϵ") → the Sosp2 problem at the instance's own accuracy (ϵG, ϵH) with ϵH² = ϵG; reason: the paper's own renaming; the same statement
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Theorem 5.1, p.22 (proof pp.22–57; PLS defined p.17)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_ConstrSOSP_LocalOpt
import Definitions.Def_ConstrSOSP_InteriorSospBox
import Definitions.Def_ConstrSOSP_Sosp1Box
import Definitions.Def_ConstrSOSP_Sosp2Box

namespace ConstrSOSP

open CardinalMatching

/-- **Theorem 5.1** (Kontogiannis, Panageas & Pollatos, *The Computational Complexity of Avoiding
Strict Saddle Points in Constrained Optimization*, arXiv:2604.02285, version of 2 November 2026,
p.22): "Interior-Sosp is PLS-hard, even when the domain is fixed to [0, 1]^2 and all regularity
promises hold. Hardness holds for finding an (ϵ, √ϵ)-SOSP with L = L1 = L2 = 1, even when every
ϵ-approximate KKT point belongs to [1/12, 11/12]^2. Consequently, finding an (ϵ, √ϵ)-SOSP1 is
PLS-hard under the same restrictions. The same statement holds for SOSP2."

Stated as a reduction closure: there is `K₀` such that for every clock exponent `K ≥ K₀`, every
search problem `Q` that reduces in polynomial time to LocalOpt also reduces in polynomial time to
each of
1. Interior-Sosp (an `(ϵG, ϵH)`-SOSP in the open square `(0, 1)²`),
2. Sosp1 (an `(ϵG, ϵH)`-SOSP1, proximal gradient with `L₁ = 1`), and
3. Sosp2 (an `(ϵG, ϵH)`-SOSP2)
on the white-box instances of `ValidBox K`: domain `[0, 1]²`, `L = L₁ = L₂ = 1`, accuracy
`(ϵ, √ϵ)` (`ϵH² = ϵG`), all regularity promises, and every `ϵG`-approximate KKT point in
`[1/12, 11/12]²`.

**Formalization Note** PLS is the class of TFNP problems reducing to LocalOpt (p.17), so the
reduction closure is PLS-hardness. Reductions are `SearchReduces` (Cook's Turing machines, correct
for every answer). White-box functions are machine codes run for `T · (|w| + 1)^K` steps, with
`T` written in unary in the instance and `K` fixed by the problem. -/
theorem theorem_5_1 :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ Q : TetrisHard.Rows.SearchProblem,
      SearchReduces Q LocalOpt →
        SearchReduces Q (InteriorSospBox K) ∧ SearchReduces Q (Sosp1Box K) ∧
          SearchReduces Q (Sosp2Box K) := by sorry

end ConstrSOSP
