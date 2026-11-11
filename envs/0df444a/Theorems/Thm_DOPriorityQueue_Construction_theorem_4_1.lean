-- Prove2me | Theorems.Thm_DOPriorityQueue_Construction_theorem_4_1
-- name    : DOPriorityQueue.Construction.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:30.725897+00:00
-- url     : https://prove2.me/theorems/e007ba4d-16b6-4f9b-a437-dc10c9d20275
-- title:
--   Theorem 4.1 — exact online differentially oblivious priority queue
-- statement:
--   Fix arbitrary constants $c>0$ and $\varepsilon>0$. There is an online word-RAM priority-queue implementation family, starting empty, with integer priorities $1\le p\le T^c$ and opaque constant-word payloads. For every public horizon $T\ge2$, it terminates on every random execution, returns exact minimum records with insertion-order tie breaking, and returns an empty answer on an empty extraction. The access trace records each server address and read/write direction and keeps external call boundaries visible.
--
--   Under replacement of at most one complete operation, including its code, priority or payload, the implementation is $(\varepsilon,\delta_T)$ differentially oblivious, where
--   $$\delta_T=2^{-\lceil\log_2T\rceil^2}.$$
--   For every fixed history of actual length $t\le T$, it uses polylogarithmically many private words at every instant, including temporary workspace, and satisfies
--   $$\mathbb E[W(h)]\le C\,t\,\frac{\log T}{\log\log T}$$
--   beyond a fixed horizon threshold. The program, word-length factors, positive constants $C,D$, private-space exponent and threshold are chosen for fixed $c,\varepsilon$ before $T,t$ or the history. They do not depend on priorities, outcomes, history, or horizon. Exactness and privacy hold at the small horizons too, and a zero-call history performs zero work.
--
--   The claim establishes the paper's full construction headline, including private operation codes and total client work. It does not assert the independent lower bound. The milestones of this mission are Lemmas 5.1 and 5.2, the reflection identity for live prefix counts and the cutoff lemma for exact prefetching.
--
--   Differences from the source:
--   - encoding: integer priorities in [T^c] → priorities 1 through floor(T^c); reason: the domain contains exactly the source integer priorities, including when 0 < c < 1
--   - encoding: standing T ≥ 2; asymptotic work and polylogarithmic private words → exactness and privacy for all T ≥ 2; resource constants and threshold ≥ 16 preceding T and every history; reason: preserves the uniform asymptotic meaning and avoids evaluating log T / log log T at its singular small horizons
--   - encoding: word-RAM with opaque payloads, w = Θ(log T)-bit words, charged client instructions and server probes → finite instruction lists, modular fixed-width words of length scale·⌈log₂T⌉ + offset for existentially chosen positive integers scale, offset, sixteen data registers and opaque atomic cells; derived work and peak footprints; reason: an explicit instruction and calling convention; fixed per-instruction and input/output factors are absorbed by the uniform constants
--   - encoding: internal independent uniform random words; all measurable trace events → nonnegative sums of terminal random-word cylinder masses; discrete sets of call-grouped traces; reason: equivalent probability semantics for finite terminating executions; the normalized-law and every-tape requirements exclude missing mass
--   - encoding: logarithmic asymptotic rate → natural-log rate; integer horizon parameters use base two; reason: the rate changes only by uniform asymptotic factors; the exact privacy delta retains base two
--   - reading: "Fix constants c, ε > 0 and T ∈ N+ … There is … Q" (Q named after T) → one finite program, receiving the public T and U = ⌊T^c⌋ in registers, serves every T ≥ 2; reason: the O(·) bounds only have content uniformly in T, and the construction computes its parameters from the public T at run time (pp. 26 and 36–37); the uniform program specializes to a queue for each fixed T
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 6, Theorem 4.1; pp. 26–27, proof; pp. 2–4, standing model; pp. 36–37, instructions

import Definitions.Def_DOPriorityQueue_Construction_Target

set_option autoImplicit false

namespace DOPriorityQueue.Construction

/-- Guo--Hong--Li, STOC 2027 submission #538 (October 2026), p. 6,
Theorem 4.1; standing model from Section 2 and Appendix B.
The target does not presuppose any of the construction's guarantees. -/
theorem theorem_4_1 (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    HeadlineTarget c ε := by sorry

end DOPriorityQueue.Construction
