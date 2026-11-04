-- Prove2me | Theorems.Thm_CappedBaseStock_policy_window_relaxation
-- name    : CappedBaseStock.policy_window_relaxation
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T02:24:40.164532+00:00
-- url     : https://prove2.me/theorems/6a8ff901-ff7a-4497-9cbe-02799e1663f4
-- title:
--   Near-optimal independent inventory windows at both horizons
-- statement:
--   Consider the mission's lost-sales inventory model with integer lead time $L\ge1$, holding cost $h>0$, lost-sales penalty $p>0$, and i.i.d. nonnegative demands of finite mean $\mu>0$. Let $\pi$ be any admissible measurable history-dependent randomized policy, started from zero inventory and an empty pipeline, with finite limsup expected average cost $C(\pi)$.
--
--   For every $\varepsilon>0$, there exist an integrable nonnegative input vector $(I_0,A_0,\ldots,A_L)$, independent of a fresh demand sequence, and real numbers $r,z$, such that
--
--   $$
--   0\le r\le\mu,\qquad z\ge0,\qquad
--   \mathbb E[I_0]=z,\qquad \mathbb E[A_i]=r\quad(0\le i\le L),
--   $$
--
--   and, for the recursion $I_{k+1}=(I_k+A_k-D_k)^+$,
--
--   $$
--   \mathbb E[I_L]\le z,\qquad
--   \mathbb E[I_{L+1}]\le z,\qquad
--   hz+p(\mu-r)\le C(\pi)+\varepsilon.
--   $$
--
--   This auxiliary existence theorem supplies the independent inventory window needed for both horizon constraints in Proposition 1. It is a new approximate formulation of the manuscript's stationary-policy step: it does not assert that the original optimum is attained. Its scope includes the full policy class and both horizons, so it is an additional obligation beyond the cited 2016 theorem's $L$-window conclusion.
--
--   **Formalization Note** Policy cost and the final cost comparison take values in the extended nonnegative reals; finiteness of the given policy cost is explicit. Window coordinates have finite real first moments, and independence from demands is represented by a product measure.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, user-supplied 2026 manuscript, Proposition 1 (label lemma-lb), source-manuscript.tex lines 253-303; SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Equations eq-stationary-cost, eq-envelope-L and eq-envelope-L+1; new epsilon/per-policy window-relaxation obligation replacing the assumed stationary optimal regime, with both horizons retained. Related background: Xin and Goldberg, Optimality Gap of Constant-Order Policies Decays Exponentially in the Lead Time for Lost Sales Models, Operations Research 64(6), 1556-1565 (2016), DOI 10.1287/opre.2016.1514; author-hosted April 2016 manuscript https://people.orie.cornell.edu/dag369/ftp/Goldberg_Xin_Lost_Sales_Constant_Order_Expofast_4_2016.pdf, Theorem 2 on printed page 9, Observation 1 on printed page 10, and Appendix 5.3. The 2016 statement does not itself include the extra current-order coordinate, the L+1 endpoint bound, deterministic demand, or the full randomized history-policy class; the required extension is part of this open problem.

import Definitions.Def_CappedBaseStock_Window

open scoped ENNReal

namespace CappedBaseStock

theorem policy_window_relaxation (P : DemandLaw) (c : Parameters)
    (π : AdmissiblePolicy) (hfinite : policyCost P c π < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : WindowLaw (c.L + 1), ∃ r z : ℝ,
      0 ≤ r ∧ r ≤ mean P ∧ 0 ≤ z ∧ WindowMeans W r z ∧
      windowExpectedInventory P W c.L ≤ ENNReal.ofReal z ∧
      windowExpectedInventory P W (c.L + 1) ≤ ENNReal.ofReal z ∧
      certificateObjective P c r z ≤ policyCost P c π + ENNReal.ofReal ε := by sorry

end CappedBaseStock
