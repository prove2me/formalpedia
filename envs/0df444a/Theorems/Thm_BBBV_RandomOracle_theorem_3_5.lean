-- Prove2me | Theorems.Thm_BBBV_RandomOracle_theorem_3_5
-- name    : BBBV.RandomOracle.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:57.865995+00:00
-- url     : https://prove2.me/theorems/c4c02663-9a65-4448-9278-5124871a0529
-- title:
--   Theorem 3.5, p. 8 — a quantum algorithm with T ≤ c·2^{n/2} queries fails on ≥ 1/8 of the oracles to decide whether 1ⁿ has a preimage
-- statement:
--   There are a constant $c > 0$ and a threshold $N$ such that the following holds for every $n \ge N$. Let $M$ be any quantum algorithm (with any finite workspace) that makes $T \le c \cdot 2^{n/2}$ queries to an oracle $A : \{0,1\}^n \to \{0,1\}^n$. Choose $A$ uniformly at random among all $(2^n)^{2^n}$ such functions. Then
--   $$\Pr_A\bigl[\, M \text{ with oracle } A \text{ fails to decide whether } \exists x,\ A(x) = 1^n \,\bigr] \ge \frac18 ,$$
--   where "decide" means: accept with probability at least $2/3$ if $1^n$ has a preimage, and at most $1/3$ if it does not.
--
--   This is the finite core of the paper's Theorem 3.5, "for any $T(n)$ which is $o(2^{n/2})$, relative to a random oracle, with probability $1$, $\mathbf{BQTime}(T(n))$ does not contain $\mathbf{NP}$": the language $\mathcal{L}_A = \{y : \exists x\, A(x) = y\}$ is in $\mathbf{NP}^A$, and the theorem shows that no bounded-error quantum algorithm recognises it on input $1^n$ with $o(2^{n/2})$ queries. Grover's algorithm shows that $O(2^{n/2})$ queries suffice, so the bound is tight up to the constant.
--
--   **Formalization Note** The statement is in the query model (see the definitions file): every oracle QTM running $T$ steps is a $T$-query algorithm, oracle answers on lengths other than $n$ are fixed and absorbed into the unitaries (the page proves the bound "for every way of fixing the oracle answers on inputs of length not equal to $n$"), and the input $1^n$ is absorbed into the initial state. Queries return the full value $A(x) \in \{0,1\}^n$; since one Boolean query is simulated by two full-value queries, the statement implies the bound for the paper's Boolean oracle with $c$ halved. The constant is existential: the page picks $T(n) \le 2^{n/2}/20$, but with the paper's own count ($338\,T^2$ strings from Corollary 3.4 at $\varepsilon = 1/13$) that choice gives $\mathrm{card}(S) \le 0.845 \cdot 2^n$ and the step $2^n - \mathrm{card}(S) \ge 2^{n-1}$ fails; with the corrected Corollary 3.4 ($676\,T^2$ strings) the argument works for $T \le 2^{n/2}/37$. The hypothesis $T(n) = o(2^{n/2})$ of the theorem is exactly "below $c \cdot 2^{n/2}$ for some $c > 0$ eventually". The closing step of the paper — a probability-$1$ statement over countably many machines and all $n$ — is not formalized. The constant $c$ and the threshold $N$ do not depend on the workspace or on the algorithm.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 8, Theorem 3.5 (proof pp. 8–10; the finite claim on p. 9, second paragraph)

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

open Classical in
theorem theorem_3_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ), (T : ℝ) ≤ c * Real.sqrt (2 ^ n) →
      ∀ M : QueryAlg (Str n) (Str n) W T,
        (1 / 8 : ℝ) ≤
          ((Finset.univ.filter fun A : Str n → Str n =>
              ¬ Decides M (fun _ => A) (∃ x, A x = ones n)).card : ℝ) /
            (Fintype.card (Str n → Str n) : ℝ) := by sorry

end BBBV.RandomOracle
