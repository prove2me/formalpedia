-- Prove2me | Theorems.Thm_FSS23105365_chain_to_dfa
-- name    : FSS23105365.chain_to_dfa
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T15:55:26.604823+00:00
-- url     : https://prove2.me/theorems/c1c84d7d-e5e1-44e5-b024-b5ab80579f7b
-- title:
--   Lemma E.3 — binary DFA representation of a transition-dyadic chain
-- statement:
--   For every natural number $q$ and every Markov chain $M$ on the state set $\{0,\ldots,q-1\}$, with nonnegative real initial weights summing to one and nonnegative real transition weights whose every row sums to one, assume that each initial weight and every transition weight equals $a/2^b$ for some natural numbers $a,b$ that may depend on the weight. There exist a natural number $r$, a deterministic binary automaton $B$ with state set $\{0,\ldots,r-1\}$, a specified initial state, a transition function for each state and Boolean input, and an accepting set, positive natural numbers $v,s$, and a function $\varphi$ from the states of $B$ to the states of $M$, such that for every natural number $n$ and every sequence $\gamma=(\gamma_0,\ldots,\gamma_n)$ of states of $M$, the fraction of all $2^{v+ns}$ binary words $x$ of length $v+ns$ satisfying $\varphi(B\text{'s state after reading the first }v+si\text{ bits of }x)=\gamma_i$ for every $i=0,\ldots,n$ is exactly $M_{\mathrm{initial}}(\gamma_0)\prod_{i=0}^{n-1}M_{\mathrm{transition}}(\gamma_i,\gamma_{i+1})$. The witnesses $r,B,v,s,\varphi$ are chosen once for all $n$ and all sequences $\gamma$, including sequences of probability zero. The accepting set of $B$ is not used in the equality. When $n=0$, the equality concerns the distribution of the projected state after $v$ bits and its right-hand side is the initial weight of $\gamma_0$. Although positivity of $q$ and $r$ is not an explicit separate requirement, the normalized initial distribution of $M$ rules out $q=0$, and the specified initial state of $B$ rules out $r=0$. No numerical bounds on $r,v,s$ or algorithm for obtaining the witnesses are asserted.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang. Revision Provably Reduces Sequential Computation in Diffusion Language Models. https://doi.org/10.5281/zenodo.23105365, Appendix E. Lemma E.3; the equality of complete projected trajectories at fixed block boundaries.

import Definitions.Def_FSS23105365_DFARun
set_option autoImplicit false
open FSS23105365

namespace FSS23105365
theorem chain_to_dfa {q : ℕ} (M : MarkovChain q)
    (hM : TransitionDyadic M) :
    ∃ r : ℕ, ∃ B : BinaryDFA r, ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
      ∃ φ : Fin r → Fin q, ∀ n : ℕ, ∀ γ : Path q n,
        (Fintype.card {x : Bits (v + n * s) // B.sampledPath φ v s x = γ} : ℝ) /
          2 ^ (v + n * s) = pathLaw M γ := by sorry
end FSS23105365
