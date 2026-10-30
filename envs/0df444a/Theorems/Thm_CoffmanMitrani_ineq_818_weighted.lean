-- Prove2me | Theorems.Thm_CoffmanMitrani_ineq_818_weighted
-- name    : CoffmanMitrani.ineq_818_weighted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:28:09.027968+00:00
-- url     : https://prove2.me/theorems/550ecf09-94ea-431a-bf43-b0904887dd48
-- title:
--   Proof of Lemma 2: second displayed inequality
-- statement:
--   Let $g_1, g_2$ be sets of classes, $g_{12} = g_1\cap g_2$, $G_{12} = g_1\cup g_2$, $h_1 = g_1-g_{12}$, $h_2 = g_2-g_{12}$, and $a_i = \rho_i/\mu_i$. If $h_1$ and $h_2$ are nonempty, then
--   $$\Big(\sum_{g_1} a_i\Big)\Big(1-\sum_{g_2}\rho_i\Big) + \Big(\sum_{g_2} a_i\Big)\Big(1-\sum_{g_1}\rho_i\Big) - \Big(\sum_{g_{12}} a_i\Big)\Big(1-\sum_{G_{12}}\rho_i\Big) < \Big(\sum_{G_{12}} a_i\Big)\Big(1-\sum_{g_{12}}\rho_i\Big).$$
--
--   Differences from the source:
--   - encoding: classes 1, …, M and the nth arriving job of class i → classes Fin M and job index n : ℕ, both 0-based; reason: Lean indexing; the same objects
--   - encoding: M classes, Poisson rates λi, exponential parameters μi, equilibrium assumed (ρ < 1) → Data with 1 ≤ M, 0 < λi, 0 < μi and Σ λi/μi < 1; reason: the rates of a Poisson stream and of an exponential law are positive, M = 0 has no classes, and ρ < 1 is the paper's standing equilibrium assumption (pp. 812–813)
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2 (unnumbered display)

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_rho

namespace CoffmanMitrani

/-- **Second displayed inequality in the proof of Lemma 2.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2 (unnumbered display): "(Σ_{i∈g1} ai)(1 − Σ_{i∈g2} ρi) +
(Σ_{i∈g2} ai)(1 − Σ_{i∈g1} ρi) − (Σ_{i∈g12} ai)(1 − Σ_{i∈G12} ρi) < (Σ_{i∈G12} ai)(1 − Σ_{i∈g12} ρi)
when h1 and h2 are nonempty", where "ai = ρi/μi, i = 1, 2, ···, M".

For sets of classes `g1, g2` with `g1 \ g2` and `g2 \ g1` nonempty, writing `a i = ρi/μi`,
`g12 = g1 ∩ g2`, `G12 = g1 ∪ g2`, the inequality above holds. -/
theorem ineq_818_weighted (D : Data) (g1 g2 : Finset (Fin D.M))
    (h1 : (g1 \ g2).Nonempty) (h2 : (g2 \ g1).Nonempty) :
    (∑ i ∈ g1, D.rho i / D.mu i) * (1 - ∑ i ∈ g2, D.rho i) +
        (∑ i ∈ g2, D.rho i / D.mu i) * (1 - ∑ i ∈ g1, D.rho i) -
        (∑ i ∈ g1 ∩ g2, D.rho i / D.mu i) * (1 - ∑ i ∈ g1 ∪ g2, D.rho i) <
      (∑ i ∈ g1 ∪ g2, D.rho i / D.mu i) * (1 - ∑ i ∈ g1 ∩ g2, D.rho i) := by sorry

end CoffmanMitrani
