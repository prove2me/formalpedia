-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_conservation_polytope_eq_priority_hull
-- name    : CoffmanMitrani1980.Region.conservation_polytope_eq_priority_hull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:16:44.882841+00:00
-- url     : https://prove2.me/theorems/d63f0fef-c628-43e5-a3f7-7638b2d95216
-- title:
--   Theorem 2 (analytical form) — H** = H: (1) and (4) characterize the hull of the preemptive priority vectors
-- statement:
--   Fix $M\ge1$ job classes with arrival rates $\lambda_i>0$, service rates $\mu_i>0$, $\rho_i=\lambda_i/\mu_i$ and $\rho=\sum_i\rho_i<1$. A vector $W\in\mathbb R^M$ satisfies the conservation law and the $2^M-2$ inequalities
--   $$\sum_{i=1}^M\rho_iW_i=\frac{\sum_{i=1}^M\lambda_i/\mu_i^2}{1-\rho},\qquad \sum_{i\in g}\rho_iW_i\ge\frac{\sum_{i\in g}\rho_i/\mu_i}{1-\sum_{i\in g}\rho_i}\ \ (\emptyset\ne g\subsetneq\{1,\dots,M\}),$$
--   if and only if there are $M$ preemptive priority vectors $P_1,\dots,P_M$ and weights $\alpha_k\ge0$ with $\sum_k\alpha_k=1$ and $W=\sum_k\alpha_kP_k$. That is, $H^{**}=H$.
--
--   In the paper this is the analytical half of Theorem 2: the set $H^*$ of response-time vectors achievable by a scheduling strategy satisfies $H\subseteq H^*\subseteq H^{**}$, so $H^{**}=H$ gives $H^*=H$ and the test "check (1) and (4)" for achievability.
--
--   **Formalization Note.** The achievable set $H^*$ rests on a strategy class described only in prose, so the statement is the part $H^{**}=H$ of the chain that involves no strategies. $M\ge1$ is needed, since for $M=0$ the set $H$ is empty.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, p. 816, Theorem 2; p. 817 ("Lemmas 1 and 2 imply that H* ⊆ H** ⊆ H"); p. 818 ("The equation H* = H** provides us with an analytical characterization of H*"); (3), p. 815

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- **Theorem 2, analytical form** — Coffman and Mitrani, Operations Research 28 (1980), p. 816
(PDF 8), Theorem 2, with p. 817 (PDF 9) "Lemmas 1 and 2 imply that H\* ⊆ H\*\* ⊆ H" and p. 818
(PDF 10) "The equation H\* = H\*\* provides us with an analytical characterization of H\*": a vector
`W` satisfies the conservation law (1) and the `2^M - 2` inequalities (4) if and only if it is a
convex combination `Σ αᵢ Pᵢ` of `M` preemptive priority vectors, as in (3); that is, `H** = H`.

**Formalization Note.** The paper's Theorem 2 is `H* = H`, where H\* is the set of performance
vectors achievable by a scheduling strategy of the class of Assumptions 1–3 (p. 812). That class is
described only in prose, so H\* is replaced by its analytical characterization H\*\*, and the
statement is the part `H** = H` of the chain `H ⊆ H* ⊆ H** ⊆ H` that does not involve strategies.
`0 < M` is needed: for `M = 0`, H is empty (no weights sum to 1) while H\*\* is a point. -/
theorem conservation_polytope_eq_priority_hull {M : ℕ} (hM : 0 < M) (p : Params M) :
    p.Hss = p.H := by sorry

end CoffmanMitrani1980.Region
