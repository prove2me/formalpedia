-- Prove2me | Theorems.Thm_EvenCycleListing723_Main_lemma_3_1
-- name    : EvenCycleListing723.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:22.192149+00:00
-- url     : https://prove2.me/theorems/9da91bea-3eac-4183-af65-a040fbf52a47
-- title:
--   Lemma 3.1 — randomized and deterministic listing with exploration cost
-- statement:
--   Fix an integer $k\ge2$, and let $G$ be any $n$-vertex simple undirected graph. Put $t=t_{2k}(G)$ and let $W_k(G)$ be the sum of current degrees over the radius-$(k-1)$ neighborhood of every root processed in the specified maximum-degree deletion procedure. There is a finite deterministic program implementing the BFS, backward-pruning and depth-first listing procedure, including construction of a perfect hash family and duplicate removal, that outputs every cycle exactly once in
--
--   $$\widetilde O_k\bigl(n^2+t+W_k(G)\bigr)$$
--
--   measured RAM time. Its constructed family has at most $A_k(1+\lfloor\log_2\max(2,n)\rfloor)$ members, and every palette permutation is enumerated.
--
--   The randomized version has the same bound for every tape, including its padded palette draws. For every positive integer confidence exponent $c$, choose
--
--   $$R_{k,c}(n)=\left\lceil(2k+c+1)(2k-1)^{2k-1}\log n\right\rceil.$$
--
--   For $n\ge2$ its probability of listing all cycles is at least $1-n^{-c-1}$, hence at least $1-n^{-c}$. A fixed oriented cycle is realized with probability $(2k-1)^{-(2k-1)}$ per trial; the displayed confidence follows from the source's union bound over at most $n^{2k}$ cycles. Integer $c$ is cofinal in positive real exponents. For $n<2$, the computed output is deterministically empty and complete.
--
--   Both runtime bounds mean $C(1+n^2+t+W_k(G))\ell(n)^q$ primitive steps, where $\ell(n)=1+\lfloor\log_2\max(2,n)\rfloor$. Programs and positive width and time constants are chosen before $n,G$, and random tapes; they depend only on $k$, and on $c$ in the randomized clause. The deterministic input contains no family, output list or $t$. This lemma connects the actual listing operation to the combinatorial exploration quantity.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), or Fin m with m ≤ n; reason: every finite vertex set can be relabeled; SimpleGraph imposes precisely simplicity and undirectedness
--   - encoding: unoriented noninduced cycle copies → edge sets of simple closed walks, with canonical dihedral vertex lists for output; reason: rotation and reversal identify the same copy; different cyclic edge orders remain distinct and chords are allowed
--   - reading: algorithmic time with no machine syntax specified → finite-program word RAM using the published instruction interpreter and signed words of every width at least b(1+floor(log₂(max(2,n)))); reason: this fixes standard random-access execution; each executed instruction including output stores is charged and constants are chosen before the input
--   - encoding: soft-O_k(n²+t), and soft-O_k(n²+t+W) in Lemma 3.1 → C(1+n²+t)(1+floor(log₂(max(2,n))))^q, with W added for Lemma 3.1; reason: a change of logarithm base and small-input padding preserve the rate; C,b,q depend only on k, or k,c in the random clause
--   - encoding: arbitrary total tie order and a perfect family on each explored neighborhood → label-order ties and one constructed global perfect family restricted to each neighborhood, with all palette permutations; reason: any fixed order is allowed; restriction preserves perfection and table construction and writes are included in the measured run
--   - reading: random color coding repeated O_k(log n) times with high probability → for every integer c>0 use R=ceil((2k+c+1)(2k−1)^{2k−1} log n) independent palette colorings, with failure at most n^{−c−1}; reason: one oriented cycle has probability (2k−1)^{−(2k−1)} per trial; the union bound over at most n^{2k} cycles gives the displayed rate; integer c is cofinal in all positive real confidence exponents
--   - encoding: independent uniform color choices → a finite uniform palette tape indexed by root, repetition, and vertex, with R supplied as repetition control and every padded draw charged; reason: R is determined only by k,c,n and reveals no cycles; tape reading uses RAM loads, n²R draws add only O_k,c(n² log n), and n<2 has an empty-output branch
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723 (October 2026), p.4, Lemma 3.1; random repetition and derandomization details p.5; canonical PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf (SHA256 653ba349d1e9c1a87fe327137dddf959c6871a48cf5a052e91a47e341e9e9d8f)

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_Execution

set_option autoImplicit false

namespace EvenCycleListing723.Main

/-- Lemma 3.1, pp.4–5: both clauses, worst-case measured time, and the explicit
union-bound confidence. Positive integer c gives every positive real confidence exponent. -/
theorem lemma_3_1 (k : ℕ) (hk : 2 ≤ k) :
    (∃ (P : Program) (C b q A : ℕ), 0 < C ∧ 0 < b ∧ 0 < A ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ), requiredWidth b n ≤ W →
        ∃ (t : ℕ) (F : List (Fin n → Fin (2 * k - 1))),
          deterministicProcedureRun P k G W t F ∧
          F.length ≤ A * logarithmicSize n ∧
          t ≤ softBudget C q n (n ^ 2 + cycleCount G k + exploration G k)) ∧
    (∀ (c : ℕ), 0 < c → ∃ (P : Program) (C b q : ℕ), 0 < C ∧ 0 < b ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ), requiredWidth b n ≤ W →
        (∀ ω : RandomTape n k (repetitions k c n), ∃ t : ℕ,
          randomizedProcedureRun P G ω W t ∧
          t + randomDrawCost n (repetitions k c n) ≤
            softBudget C q n (n ^ 2 + cycleCount G k + exploration G k)) ∧
        (2 ≤ n → 1 - 1 / (n : ℝ) ^ (c + 1) ≤ successProbability G k (repetitions k c n)) ∧
        (n < 2 → ∀ ω : RandomTape n k (repetitions k c n),
          correctListing G k (listingProcedure G k (randomColorings ω)))) := by sorry

end EvenCycleListing723.Main
