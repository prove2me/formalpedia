-- Prove2me | Theorems.Thm_CoffmanMitrani_ineq_818_product
-- name    : CoffmanMitrani.ineq_818_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:27:30.250311+00:00
-- url     : https://prove2.me/theorems/fc6b9ade-bc2c-42ec-9023-46702e5726f4
-- title:
--   Proof of Lemma 2: first displayed inequality
-- statement:
--   Let $g_1, g_2$ be sets of classes and write $g_{12} = g_1\cap g_2$, $G_{12} = g_1\cup g_2$, $h_1 = g_1 - g_{12}$, $h_2 = g_2 - g_{12}$. If $h_1$ and $h_2$ are nonempty, then
--   $$\Big(1-\sum_{i\in g_1}\rho_i\Big)\Big(1-\sum_{i\in g_2}\rho_i\Big) > \Big(1-\sum_{i\in G_{12}}\rho_i\Big)\Big(1-\sum_{i\in g_{12}}\rho_i\Big).$$
--
--   Together with the next inequality it shows that the right-hand side of (4) is strictly supermodular, which forces the tight sets of a vertex of $H^{**}$ to be nested.
--
--   Differences from the source:
--   - encoding: classes 1, …, M and the nth arriving job of class i → classes Fin M and job index n : ℕ, both 0-based; reason: Lean indexing; the same objects
--   - encoding: M classes, Poisson rates λi, exponential parameters μi, equilibrium assumed (ρ < 1) → Data with 1 ≤ M, 0 < λi, 0 < μi and Σ λi/μi < 1; reason: the rates of a Poisson stream and of an exponential law are positive, M = 0 has no classes, and ρ < 1 is the paper's standing equilibrium assumption (pp. 812–813)
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2 (unnumbered display)

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_rho

namespace CoffmanMitrani

/-- **First displayed inequality in the proof of Lemma 2.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2 (unnumbered display): "(1 − Σ_{i∈g1} ρi)(1 − Σ_{i∈g2} ρi) >
(1 − Σ_{i∈G12} ρi)(1 − Σ_{i∈g12} ρi) when h1 and h2 are nonempty", where "g12 = g1 ∧ g2,
G12 = g1 ∨ g2, h1 = g1 − g12 and h2 = g2 − g12".

For sets of classes `g1, g2` with `g1 \ g2` and `g2 \ g1` nonempty,
`(1 − Σ_{g1 ∪ g2} ρi)(1 − Σ_{g1 ∩ g2} ρi) < (1 − Σ_{g1} ρi)(1 − Σ_{g2} ρi)`. -/
theorem ineq_818_product (D : Data) (g1 g2 : Finset (Fin D.M))
    (h1 : (g1 \ g2).Nonempty) (h2 : (g2 \ g1).Nonempty) :
    (1 - ∑ i ∈ g1 ∪ g2, D.rho i) * (1 - ∑ i ∈ g1 ∩ g2, D.rho i) <
      (1 - ∑ i ∈ g1, D.rho i) * (1 - ∑ i ∈ g2, D.rho i) := by sorry

end CoffmanMitrani
