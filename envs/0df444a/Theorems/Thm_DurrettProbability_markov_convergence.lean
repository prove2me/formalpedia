-- Prove2me | Theorems.Thm_DurrettProbability_markov_convergence
-- name    : DurrettProbability.markov_convergence
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:25:48.188538+00:00
-- url     : https://prove2.me/theorems/3dd9a79f-f6cb-44f3-ac02-99ce4e7b219c
-- title:
--   Theorem 5.6.6 — the convergence theorem
-- statement:
--   Let $p$ be a transition probability on a countable state space that is
--
--   1. **irreducible** — $\rho_{xy}>0$ for every pair of states,
--   2. **aperiodic** — every state has period one, the greatest common divisor of
--      $I_x=\{n\ge1:p^n(x,x)>0\}$ being $1$, and
--   3. equipped with a **stationary distribution** $\pi$.
--
--   Then for all states $x$ and $y$,
--   $$p^n(x,y)\longrightarrow\pi(y)\qquad (n\to\infty).$$
--
--   The chain forgets its starting point: the distribution after $n$ steps converges to $\pi$ whatever
--   it was at time zero. This is what makes a stationary distribution a long-run frequency rather than
--   merely a fixed point of a linear map, and it is the theorem underlying Markov chain Monte Carlo,
--   card shuffling, and the equilibrium analysis of queueing and inventory models.
--
--   Both hypotheses are needed and neither can be dropped. Without irreducibility the limit depends on
--   which part of the state space the chain starts in. Without aperiodicity, $p^n(x,y)$ oscillates: a
--   chain alternating between two halves of its state space never forgets the parity of the clock, and
--   Durrett's Theorem 5.7.2 gives the corrected statement for that case. Periodicity, as the book puts
--   it, is the only thing that can prevent convergence.
--
--   The standard proof is a coupling on $S\times S$: run two independent copies, one from $x$ and one
--   from $\pi$, under $\bar p\bigl((x_1,x_2),(y_1,y_2)\bigr)=p(x_1,y_1)p(x_2,y_2)$. Aperiodicity and
--   irreducibility make the product chain irreducible, $\pi\times\pi$ is stationary for it, so the two
--   copies meet with probability one, and after they meet they may be exchanged.
--
--   **Formalization Note** The conclusion is pointwise convergence of the transition probabilities, not
--   convergence in total variation and not with a rate; those are strengthenings and are listed under
--   contributions. The transition probability is a function on a countable type with non-negative
--   entries, summable rows and rows summing to one, and every quantity involved is defined by a
--   recursion on the matrix rather than through a measure on path space.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 313 (PDF p. 321), Theorem 5.6.6: 'Convergence theorem. Suppose p is irreducible, aperiodic (i.e., all states have d_x = 1), and has stationary distribution pi. Then, as n -> infinity, p^n(x,y) -> pi(y).' Proof: 'Let S_2 = S x S. Define a transition probability p-bar on S x S ...'. The period is defined on p. 312: 'Let x be a recurrent state, let I_x = {n >= 1 : p^n(x,x) > 0}, and let d_x be the greatest common divisor of I_x. d_x is called the period of x.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

open Filter

namespace DurrettProbability

theorem markov_convergence {S : Type*} [Countable S] [DecidableEq S]
    (p : S → S → ℝ) (hp : IsTransition p) (hirr : Irreducible p)
    (haper : ∀ x, Aperiodic p x) (π : S → ℝ) (hπ : StationaryDist p π) (x y : S) :
    Tendsto (fun n : ℕ => stepProb p n x y) atTop (nhds (π y)) := by sorry

end DurrettProbability
