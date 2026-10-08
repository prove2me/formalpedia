-- Prove2me | Theorems.Thm_DistVerif_Simulation_theorem_3_1
-- name    : DistVerif.Simulation.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:50.149979+00:00
-- url     : https://prove2.me/theorems/665dba51-7763-4ce8-b3e6-cd5e1b24aebf
-- title:
--   Theorem 3.1 (Simulation Theorem) — $R^{cc-pub}_\epsilon(f)\le 2dpB\,R^{G(\Gamma,d,p)}_\epsilon(f)$ when $R^{G(\Gamma,d,p)}_\epsilon(f)<(d^p-1)/2$
-- statement:
--   Let $\Gamma,d,p,B,b$ be natural numbers with $d^p\ge1$, let $\epsilon\ge0$, and let $f:\{0,1\}^b\times\{0,1\}^b\to\{0,1\}$. Consider the network $G(\Gamma,d,p)$ of §3.1 in the B model, with Alice's input $x$ at $s=u^p_0$ and Bob's input $y$ at $r=u^p_{d^p-1}$. Suppose a public-coin randomized distributed algorithm on $G(\Gamma,d,p)$ computes $f$ with $\epsilon$-error (both $s$ and $r$ output $f(x,y)$ with probability at least $1-\epsilon$, for every input) within $T$ rounds, where
--   $$T<\frac{d^p-1}{2}.$$
--   Then there is a public-coin two-party protocol that computes $f$ with $\epsilon$-error using at most
--   $$2\,d\,p\,B\,T$$
--   bits of communication. In terms of complexities: if $R^{G(\Gamma,d,p)}_\epsilon(f)<(d^p-1)/2$, then
--   $$R^{cc-pub}_\epsilon(f)\le 2dpB\,R^{G(\Gamma,d,p)}_\epsilon(f).$$
--
--   This is the Simulation Theorem of Das Sarma et al. Combined with lower bounds on the communication complexity of set disjointness and equality, it yields the lower bounds of §§4–7 for distributed verification and approximation problems: an algorithm faster than half the path length must squeeze $f$'s communication through the $dp$ tree edges per round.
--
--   **Formalization Note** "Within $T$ rounds" means the outputs of $s$ and $r$ are read after exactly $T$ rounds; this is equivalent to the paper's worst-case running time over inputs and random strings, since an algorithm that finishes earlier can idle. Messages are exactly $B$ bits on every directed edge in every round. The protocol sends one bit per round, so its cost is the number of bits exchanged, as in §2.2. The theorem is stated for every algorithm and gives a protocol of cost $k\le 2dpBT$; the "in other words" inequality between the minima is the corresponding statement about complexities. The hypothesis $d^p\ge1$ is needed to name $s$ and $r$; when $d^p=1$ the hypothesis $T<(d^p-1)/2$ cannot hold, and $T<(d^p-1)/2$ with $T\ge0$ forces $d^p\ge2$, hence $s\ne r$. $b$ is arbitrary (the paper assumes $b\ge1$; at $b=0$ the function $f$ is constant and the theorem still holds).
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), p. 1247, Theorem 3.1 (Simulation Theorem); proof in §3.4, p. 1250

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network
import Definitions.Def_DistVerif_Simulation_Algorithm
import Definitions.Def_DistVerif_Simulation_Protocol

namespace DistVerif.Simulation

/-- **Theorem 3.1 (Simulation Theorem)** (p. 1247). If a public-coin `ε`-error B-model
algorithm on `G(Γ, d, p)` computes `f` in `T < (d^p - 1)/2` rounds, then a public-coin
`ε`-error two-party protocol computes `f` with at most `2·d·p·B·T` bits of communication. -/
theorem theorem_3_1 (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (Fin b → Bool) → (Fin b → Bool) → Bool) (T : ℕ)
    (hT : (T : ℝ) < ((d : ℝ) ^ p - 1) / 2) (A : PubAlg (Vtx Γ d p) B b)
    (hA : A.ComputesWithin (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) T f ε) :
    ∃ k : ℕ, k ≤ 2 * d * p * B * T ∧ ∃ P : PubProtocol b, P.ComputesWithin k f ε := by sorry

end DistVerif.Simulation
