-- Prove2me | Theorems.Thm_AdInterm_SPE_theorem_3_1
-- name    : AdInterm.SPE.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:17.951971+00:00
-- url     : https://prove2.me/theorems/2741d104-5698-4c24-86d9-2fb9b9fad2aa
-- title:
--   Theorem 3.1, p. 20 — tier-t intermediaries using (z_{W_{t−1}}, ψ_{W_{t−1}}) and the seller's reserve z_{W_n} form an SPE of the symmetric k-tree
-- statement:
--   Consider the symmetric tree of a seller (tier $n+1$), $n\ge0$ tiers of intermediaries and buyers (tier $0$), in which every tier-$t$ node has $k_t\ge1$ downstream agents. Buyers' values are i.i.d. with law $V$: nonnegative, lower support end $0$, finite mean, a continuous strictly positive density, and a strictly increasing virtual value $\phi_V$. Let $W_0=V$ and $W_t=\psi_{W_{t-1}}\big(W_{t-1}^{\mathrm{FH}(k_t)}\big)$ be the anticipated reports (Definition 3.3), and suppose **Assumption 3.1**: for $t=1,\dots,n$, $W_t$ has finite mean, $W_t\mid W_t>0$ has a continuous strictly positive density on its support, and its virtual value is strictly increasing.
--
--   Consider the mechanisms
--
--   $$
--   Y_t^*(w)=\psi_{W_{t-1}}(w),\qquad r_t^*=z_{W_{t-1}}\qquad(t=1,\dots,n),\qquad r_{n+1}^*=z_{W_n}.
--   $$
--
--   Then each $(r_t^*,Y_t^*)$ belongs to $\mathcal M$, and the strategy profile in which every intermediary of tier $t$ chooses $(r_t^*,Y_t^*)$ and the seller chooses $r_{n+1}^*$, for any history, is a **subgame perfect equilibrium** (Definition A.3):
--
--   1. for every tier $t=1,\dots,n$, every history $H_t$ (any mechanisms in $\mathcal M$ for tiers $t+1,\dots,n$ and any seller reserve $r_S\ge0$), every node $I_{(t,j)}$ and every mechanism $(r,Y)\in\mathcal M$, the expected profit of $I_{(t,j)}$ with $(r,Y)$ is at most its expected profit with $(r_t^*,Y_t^*)$;
--   2. for every reserve $r_S\ge0$, the seller's expected revenue with $r_S$ is at most that with $r_{n+1}^*$.
--
--   This is the paper's equilibrium characterization: in a symmetric tree each intermediary bids the projected virtual value of its highest downstream report, and every later result of the paper is stated at this equilibrium.
--
--   **Formalization Note** (i) Strict increase of $\phi_V$ is an explicit hypothesis: Assumption 3.1 lists $t=1,\dots,n$ only, but $\psi_V$ (Definition 3.2) and Lemma 3.1, used in the base case, require it. (ii) Payments are Definition A.1's minimum winning report. The closed form (2) is not used: with a deterministic tie rule it can charge less than the true threshold after an upstream reporting function that is flat on an interval, and the theorem would then fail for a deviation with a jump. (iii) Ties go to the lowest index; a report equal to a reserve wins; "reports zero" below the reserve is no report. (iv) Buyers report truthfully (Lemma 2.1(B)). (v) The seller's reserves range over $\mathbb R_+$ (p. 12), a superset of Definition A.2's $\mathcal S_{n+1}=\mathcal V$, so the seller clause is at least as strong. (vi) The profile is history-independent; for such a profile Definition A.3 is exactly the displayed inequalities, because after $H_t$ a strategy affects its owner's payoff only through the mechanism it selects at $H_t$, and the lower tiers do not react. (vii) Expected profits are single Bochner integrals of the realized profit; the equilibrium profit is nonnegative pointwise, so a non-integrable deviation (value $0$) never violates the inequality. Deviations range over all of $\mathcal M$, so the equilibrium property cannot hold for want of competitors: with rate-one exponential values and $n=1$, $k=(1,1)$, the intermediary earns $e^{-2}>0$.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), Theorem 3.1, p. 20; Assumption 3.1, p. 19; Definition A.3, p. 44; proof pp. 36–37

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

open MeasureTheory

namespace AdInterm.SPE

theorem theorem_3_1 (n : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n →
      RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t)) :
    (∀ t, 1 ≤ t → t ≤ n → IsMech (eqMech k μ t)) ∧
      IsSPE k n μ (eqMech k μ) (zproj (annLaw k μ n)) := by sorry

end AdInterm.SPE
