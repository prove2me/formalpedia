-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_part_I_limit_solution
-- name    : FinNetProp.Mitosis.part_I_limit_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:48.275092+00:00
-- url     : https://prove2.me/theorems/49230677-733b-413f-a7d2-e5ae8c045bf4
-- title:
--   Proof of Theorem 4.2, Part (I), p. 2808 — a limit of solutions of (2.1) along converging networks solves (2.1) for the limit network
-- statement:
--   Let $(F^n)_{n \in \mathbb N} = (N^n, z^n, L^n)$ be a sequence of financial networks converging to $\bar F = (\bar N, \bar z, \bar L)$, meaning that $N^n = \bar N$ for all sufficiently large $n$, $z^n \to \bar z$ and $L^n \to \bar L$. For each $n$ let $P^n$ solve the system (2.1) for $F^n$, and suppose $P^n \to \bar P$ entrywise. Then $\bar P$ solves the system (2.1) for $\bar F$:
--   $$\bar P \in \mathcal M(\bar N), \qquad \bar P_{ij} = \min\Big\{\bar\Pi_{ij}\Big(\bar z_i + \sum_{k \in \bar N} \bar P_{ki}\Big),\ \bar L_{ij}\Big\}, \quad i, j \in \bar N.$$
--
--   This is the closedness step in the continuity part of Part (I) of the proof of Theorem 4.2; combined with the uniqueness of solutions of (2.1) and the boundedness of $(P^n)$ it gives continuity of the proportional rule.
--
--   **Formalization Note** Convergence of networks is the criterion stated on p. 2803, with convergence of endowments, liabilities and payment matrices taken coordinatewise on $\mathbb N$ (all of them vanish outside the eventual common population). The page's "without loss of generality" passage to a convergent subsequence is replaced by assuming the convergence of $P^n$, which is exactly the situation the page's sentence concludes from.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, p. 2808, proof of Theorem 4.2, Part (I), continuity paragraph ('We have shown that P̄ is a solution to the system of equations (2.1) corresponding to the financial network F̄.')

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

open Filter Topology

theorem part_I_limit_solution (Fs : ℕ → FinNet) (F : FinNet) (hconv : NetConverges Fs F)
    (Ps : ℕ → ℕ → ℕ → ℝ) (hPs : ∀ n, IsPropSolution (Fs n) (Ps n)) (Pbar : ℕ → ℕ → ℝ)
    (hlim : ∀ i j, Tendsto (fun n => Ps n i j) atTop (𝓝 (Pbar i j))) :
    IsPropSolution F Pbar := by sorry

end FinNetProp.Mitosis
