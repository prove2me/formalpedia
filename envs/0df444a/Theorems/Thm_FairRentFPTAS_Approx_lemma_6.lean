-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_6
-- name    : FairRentFPTAS.Approx.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:45.781291+00:00
-- url     : https://prove2.me/theorems/81195f30-4915-4d36-98dd-86df8ca3b3a4
-- title:
--   Lemma 6, p. 17 — the rounded utilities have the same sign and the same zeros as the original ones
-- statement:
--   Let $\mathcal I$ be a well-formed instance, $0<\varepsilon<1$, and $\bar v_a(r,\cdot)$ the rounded utilities of $\bar{\mathcal I}$. For every agent $a$, room $r$ and rent $x\ge0$,
--   $$\bar v_a(r,x)\ge0\iff v_a(r,x)\ge0,\qquad \bar v_a(r,x)=0\iff v_a(r,x)=0.$$
--
--   Sign agreement lets Lemma 9 transfer the case split of Definition 2 between $\mathcal I$ and $\bar{\mathcal I}$.
--
--   **Formalization Note** The page says "any price $x\in\mathbb R$"; the utilities are given on rents in $\mathbb R_+$ (§2), and the statement is made for $x\ge0$, since the linear continuations below $0$ of $v$ and $\bar v$ have different slopes.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 17, Lemma 6

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 6, p. 17, for prices `x ≥ 0`: the rounded utility `v̄_a(r, x)` is nonnegative iff
`v_a(r, x)` is, and vanishes iff `v_a(r, x)` does. -/
theorem lemma_6 {n : ℕ} (I : Instance n) (ε : ℝ) (hI : Standing I) (hε : 0 < ε) (hε1 : ε < 1)
    (a r : Fin n) (x : ℝ) (hx : 0 ≤ x) :
    (0 ≤ ((roundInst ε I).v a r).eval x ↔ 0 ≤ (I.v a r).eval x) ∧
      (((roundInst ε I).v a r).eval x = 0 ↔ (I.v a r).eval x = 0) := by sorry

end FairRentFPTAS.Approx
