-- Prove2me | Theorems.Thm_DermanSeqDecisions_LinProg_taboo_identity
-- name    : DermanSeqDecisions.LinProg.taboo_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:45:11.671854+00:00
-- url     : https://prove2.me/theorems/8569d1d1-d40c-473b-bef5-a55128d312d9
-- title:
--   (4): the expected cost of a cycle from i is $(1/\pi_i)\sum_j \pi_j f(j)$
-- statement:
--   Let $\{p_{ij}\}$ be the transition probabilities of a Markov chain with finite state set $I$, all states belonging to the same class, and let $\pi$ be its stationary distribution (the unique solution of $\pi_j \ge 0$, $\pi_j = \sum_i \pi_i p_{ij}$, $\sum_j \pi_j = 1$). Let ${}_i p^{(t)}_{ij}$ be the taboo probability that $X_t = j$ and $X_s \ne i$ for $0 < s < t$, given $X_0 = i$, with ${}_i p^{(0)}_{ij} = 0$. Then for every function $f$ on $I$ and every $i \in I$, each series $\sum_t {}_i p^{(t)}_{ij}$ converges and
--   $$\sum_{t=0}^{\infty} \sum_{j \in I} {}_i p^{(t)}_{ij} f(j) = \sum_{j \in I} \sum_{t=0}^{\infty} {}_i p^{(t)}_{ij} f(j) = \frac{1}{\pi_i} \sum_{j \in I} \pi_j f(j).$$
--
--   The left side is the expected total of $f$ collected over one excursion from $i$ back to $i$. Derman uses the identity on the chain with the adjoined state $-1$ to express the expected total cost of Problem 2 through the stationary distribution.
--
--   **Formalization Note.** "All states in one class" is `JewellMRP.InfiniteStep.IsErgodic`: row-stochastic and irreducible (periodic chains allowed). The summability of the series is part of the conclusion.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 20, §3, display (4)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix

namespace DermanSeqDecisions.LinProg

/-- (4), p. 20 (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §3, display (4), unnumbered result quoted from Chung).

Let `P` be the transition matrix of a Markov chain with finite state set `I`, all states belonging
to the same class (`P` row-stochastic and irreducible), let `π` be its stationary vector (5), let
`f : I → ℝ` and `i ∈ I`. Then for every `j` the taboo probabilities `_i p^{(t)}_{ij}` are summable
in `t`, the series `∑_t ∑_j _i p^{(t)}_{ij} f(j)` converges to `∑_j ∑_t _i p^{(t)}_{ij} f(j)`, and that
value equals `(1/π_i) ∑_j π_j f(j)`.

**Formalization Note.** "All states belonging to the same class" is
`JewellMRP.InfiniteStep.IsErgodic P` (row-stochastic and `Matrix.IsIrreducible`; periodic chains
are allowed). The summability of the taboo series is part of the conclusion, so no `tsum` takes a
junk value. -/
theorem taboo_identity {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℝ) (hP : JewellMRP.InfiniteStep.IsErgodic P)
    (π : I → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary P π) (f : I → ℝ) (i : I) :
    (∀ j, Summable (fun t : ℕ => tabooProb P i t j)) ∧
    HasSum (fun t : ℕ => ∑ j, tabooProb P i t j * f j) (∑ j, ∑' t : ℕ, tabooProb P i t j * f j) ∧
    ∑ j, ∑' t : ℕ, tabooProb P i t j * f j = (1 / π i) * ∑ j, π j * f j := by sorry

end DermanSeqDecisions.LinProg
