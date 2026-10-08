-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_lemma1_priority_vector_mem
-- name    : CoffmanMitrani1980.Region.lemma1_priority_vector_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:16:20.883671+00:00
-- url     : https://prove2.me/theorems/383f4512-aa41-4457-ab91-dbaef64b79aa
-- title:
--   Lemma 1 (at the preemptive priority vectors) — every P(i₁, …, i_M) satisfies (1) and (4)
-- statement:
--   Fix the model parameters ($\lambda_i,\mu_i>0$, $\rho<1$) and a priority order $i_1,\dots,i_M$. The preemptive priority vector $W=P(i_1,\dots,i_M)$ satisfies the conservation law
--   $$\sum_{i=1}^M\rho_iW_i=\frac{V}{1-\rho},\qquad V=\sum_{i=1}^M\frac{\lambda_i}{\mu_i^2},$$
--   and, for every proper nonempty set $g$ of classes, the inequality (4)
--   $$\sum_{i\in g}\rho_iW_i\ge\frac{\sum_{i\in g}\rho_i/\mu_i}{1-\sum_{i\in g}\rho_i}.$$
--   In other words $P(i_1,\dots,i_M)\in H^{**}$, and hence $H\subseteq H^{**}$ by convexity.
--
--   **Formalization Note.** The paper states Lemma 1 for every achievable performance vector and applies it to the preemptive priority disciplines, which are achievable. The strategy class is not formalized, so this item states the content at the priority vectors, given by their closed form.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, pp. 816-817, Lemma 1 (inequalities (4)), applied to the preemptive priority disciplines as in the proof of Theorem 2, p. 816

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- Coffman and Mitrani, Operations Research 28 (1980), pp. 816–817 (PDF 8–9), Lemma 1, at the
preemptive priority vectors: every preemptive priority vector `P(i₁, …, i_M)` satisfies the
conservation law (1) and the inequalities (4) for every proper nonempty set of classes, i.e. lies in
H\*\*.

**Formalization Note.** Lemma 1 is stated in the paper for every achievable performance vector; the
proof of Theorem 2 applies it to the preemptive priority disciplines, which are achievable (p. 816).
The class of scheduling strategies is not formalized, so this item states the algebraic content at the
priority vectors, given by their closed form `prioVec`. -/
theorem lemma1_priority_vector_mem {M : ℕ} (p : Params M) (π : Equiv.Perm (Fin M)) :
    p.prioVec π ∈ p.Hss := by sorry

end CoffmanMitrani1980.Region
