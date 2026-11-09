-- Prove2me | Theorems.Thm_EvenCycleListing723_Main_theorem_1_1
-- name    : EvenCycleListing723.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:23:05.466893+00:00
-- url     : https://prove2.me/theorems/a2c7badb-1184-42a1-bf5d-ab78aff56723
-- title:
--   Theorem 1.1 — deterministic listing of all fixed-length even cycles
-- statement:
--   For every fixed integer $k\ge2$ there is a finite deterministic program that, given any finite simple undirected graph $G$ on $n$ vertices, lists all its noninduced $2k$-cycle copies. If $t_{2k}(G)$ is their number, then the program halts in
--
--   $$C_k\bigl(1+n^2+t_{2k}(G)\bigr)\bigl(1+\lfloor\log_2\max(2,n)\rfloor\bigr)^{q_k}$$
--
--   primitive word-RAM steps, for some positive constants $C_k,b_k$ and a natural exponent $q_k$ chosen before $n$ and $G$. It works at every word width at least $b_k(1+\lfloor\log_2\max(2,n)\rfloor)$. Input is only $n$ and the adjacency matrix: the number $t_{2k}(G)$ is not known in advance or supplied.
--
--   Output is an actual written length followed by canonical vertex lists, one for each distinct unoriented cycle edge set. Output writes and every operation used for construction, sorting and deduplication count toward the time bound. Chords are allowed. The guarantee includes disconnected graphs, $n=0,1$, and $n<2k$, and imposes no regularity or sparsity promise. This is the paper's deterministic all-listing headline result, including the derandomization reading in the paragraph following the theorem.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), or Fin m with m ≤ n; reason: every finite vertex set can be relabeled; SimpleGraph imposes precisely simplicity and undirectedness
--   - encoding: unoriented noninduced cycle copies → edge sets of simple closed walks, with canonical dihedral vertex lists for output; reason: rotation and reversal identify the same copy; different cyclic edge orders remain distinct and chords are allowed
--   - reading: algorithmic time with no machine syntax specified → finite-program word RAM using the published instruction interpreter and signed words of every width at least b(1+floor(log₂(max(2,n)))); reason: this fixes standard random-access execution; each executed instruction including output stores is charged and constants are chosen before the input
--   - encoding: soft-O_k(n²+t), and soft-O_k(n²+t+W) in Lemma 3.1 → C(1+n²+t)(1+floor(log₂(max(2,n))))^q, with W added for Lemma 3.1; reason: a change of logarithm base and small-input padding preserve the rate; C,b,q depend only on k, or k,c in the random clause
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723 (October 2026), p.2, Theorem 1.1 and following derandomization paragraph; proof p.8; canonical PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf (SHA256 653ba349d1e9c1a87fe327137dddf959c6871a48cf5a052e91a47e341e9e9d8f)

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_Execution

set_option autoImplicit false

namespace EvenCycleListing723.Main

/-- Theorem 1.1, p.2 (deterministic reading in the immediately following paragraph).
One finite program and constants per fixed k, before every graph and every order n. -/
theorem theorem_1_1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ (P : Program) (C b q : ℕ), 0 < C ∧ 0 < b ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (W : ℕ), requiredWidth b n ≤ W →
        ∃ t : ℕ, haltsListing P k G W t ∧
          t ≤ softBudget C q n (n ^ 2 + cycleCount G k) := by sorry

end EvenCycleListing723.Main
