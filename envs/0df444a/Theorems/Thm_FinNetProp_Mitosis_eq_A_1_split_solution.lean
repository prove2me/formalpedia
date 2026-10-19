-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_eq_A_1_split_solution
-- name    : FinNetProp.Mitosis.eq_A_1_split_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:32.442928+00:00
-- url     : https://prove2.me/theorems/e95ad825-a3d5-4ef6-a478-4eb3bbfb8b86
-- title:
--   (A.1), proof of Theorem 4.2, Part (I), pp. 2808–2809 — the split payment matrix solves (2.1) for the split network
-- statement:
--   Let $F = (N, z, L)$ be a financial network, let $P$ solve the system (2.1) for $F$, let $j \in N$, and let $K$ be a finite set of agents disjoint from $N$. Let $F' = (N', z', L')$ be the network obtained by splitting $j$ into the $|K|+1$ identical agents $\{j\} \cup K$ as in Axiom 4.1. Define $P'$ on $N' = N \cup K$ by
--   $$P'_{ki} = \frac{P_{ji}}{|K|+1},\quad P'_{ik} = \frac{P_{ij}}{|K|+1},\quad P'_{k\ell} = 0,\quad P'_{hi} = P_{hi}, \tag{A.1}$$
--   for $k, \ell \in \{j\} \cup K$ and $h, i \in N \setminus \{j\}$. Then $P' \in \mathcal M(N')$ and $P'$ solves the system (2.1) for $F'$.
--
--   This is the invariance-to-mitosis step of Part (I) of the proof of Theorem 4.2: with uniqueness of solutions it gives $p(F') = P'$ for $P = p(F)$, from which the three equations of Axiom 4.1 follow by summing.
--
--   **Formalization Note** The page states the claim for $P = p(F)$, the unique solution; it is stated here for any solution $P$ of (2.1), which is the same claim by the uniqueness milestone and is what the page's Cases A.1–A.3 verify. $P'$ is zero outside $N' \times N'$.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, pp. 2808–2809, proof of Theorem 4.2, Part (I), (A.1) and Cases A.1–A.3

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem eq_A_1_split_solution (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P)
    (j : ℕ) (hj : j ∈ F.N) (K : Finset ℕ) (hK : Disjoint K F.N) (F' : FinNet)
    (hF' : IsSplit F j K F') :
    IsPropSolution F' (splitPay F.N P j K) := by sorry

end FinNetProp.Mitosis
