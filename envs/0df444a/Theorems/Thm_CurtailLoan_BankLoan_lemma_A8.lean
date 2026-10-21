-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_lemma_A8
-- name    : CurtailLoan.BankLoan.lemma_A8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:19.030771+00:00
-- url     : https://prove2.me/theorems/d333d880-f093-4fe6-be02-cfd3c44101ec
-- title:
--   Lemma A.8 (1) and (2) on $[w^u_1, w^u_2]$, Appendix p. 20 (PDF 53) — the buyer's optimal profit and the supplier's profit as functions of $w$
-- statement:
--   Consider the model of the mission with a regular demand law under the standing assumptions, and suppose $t < t_k(w_{min})$. Then:
--
--   1. the buyer's optimal expected profit $V_B(w) = \sup\{S(Q) - wQ - \text{fee}\}$ (over the three modes and their feasible orders) is continuous and decreasing in $w \in (0, 1]$, and strictly decreasing when $l > 0$;
--   2. for every $w \in [w^u_1, w^u_2]$ with $w \ge c$ and every optimal choice of the buyer (goodwill tie-break), the supplier's profit is
--   $$(w - c)Q^* = \begin{cases} (w - c)\min\Bigl(\dfrac{v + l - \tau - t}{w},\ \bar F^{-1}(w)\Bigr), & w \in [w^t_1, w^t_2],\\[2mm] (w - c)\dfrac{u + l - \tau}{w}, & \text{otherwise.}\end{cases}$$
--
--   In the page's notation the first line is $\Pi^1_S$ on $[w^t_1, w^v_1] \cup [w^v_2, w^t_2]$ and $\Pi^3_S$ on $[w^v_1, w^v_2]$, the second is $\Pi^2_S$ on $[w^u_1, w^t_1] \cup [w^t_2, w^u_2]$. This is the shape of the supplier's objective that the equilibrium analysis maximizes.
--
--   **Formalization Note** The page states (1) on $[0, 1]$ and says "decreases"; prices are restricted to $(0, 1]$ throughout the mission. Strict decrease requires $l > 0$: if $l = 0$ and $\tau > 0$, the buyer orders nothing and earns zero at prices sufficiently close to $1$. The statement keeps the unconditional nonincrease and records strictness under positive capital. Part (2) is formalized on $[w^u_1, w^u_2]$, the region that matters for Area II, and for $w \ge c$: below $c$ the goodwill rule breaks the buyer's ties at $w^t_1, w^t_2$ towards the smaller order, and the supplier never prices there; the page's pieces outside it and its closing "moreover" chain of equalities are not formalized (two of those equalities, $\Pi^0_S(w^u_1) = \Pi^1_S(w^l_1)$ and $\Pi^2_S(w^v_1) = \Pi^3_S(w^v_1)$, do not match the definitions of $\Pi^0_S, \dots, \Pi^3_S$).
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), Appendix p. 20 (PDF 53), Lemma A.8 (1) and (2); Π^0_S–Π^3_S from Appendix pp. 14, 20 (PDF 47, 53)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Lemma A.8 (1), and (2) on `[w^u_1, w^u_2]`, Appendix p. 20 (PDF 53): for `t < tk(w_min)` the
buyer's optimal profit is continuous and decreasing in `w ∈ (0, 1]`, strictly so when
`l > 0`; on
`[w^u_1, w^u_2]` the supplier earns `(w − c) min((v+l−τ−t)/w, F̄^{-1}(w))` on `[w^t_1, w^t_2]`
and `(w − c)(u+l−τ)/w` elsewhere (for `w ≥ c`; below `c` the goodwill rule breaks ties towards
the smaller order). -/
theorem lemma_A8 (P : Params) (hR : P.Regular) (hS : Standing P)
    (ht : P.t < tk P (wmin P)) :
    (ContinuousOn (buyerValue P) (Set.Ioc 0 1) ∧
      AntitoneOn (buyerValue P) (Set.Ioc 0 1) ∧
      (0 < P.l → StrictAntiOn (buyerValue P) (Set.Ioc 0 1))) ∧
    ∀ (w : ℝ) (m : Mode) (Q : ℝ), w ∈ Set.Icc (wu1 P) (wu2 P) → P.c ≤ w → IsResponse P w m Q →
      (w ∈ Set.Icc (wt1 P) (wt2 P) →
        (w - P.c) * Q = (w - P.c) * min ((P.v + P.l - P.tau - P.t) / w) (Finv P w)) ∧
      (w ∉ Set.Icc (wt1 P) (wt2 P) → (w - P.c) * Q = (w - P.c) * (L P / w)) := by sorry

end CurtailLoan.BankLoan
