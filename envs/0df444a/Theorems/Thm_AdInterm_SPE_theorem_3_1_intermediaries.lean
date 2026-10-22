-- Prove2me | Theorems.Thm_AdInterm_SPE_theorem_3_1_intermediaries
-- name    : AdInterm.SPE.theorem_3_1_intermediaries
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T18:34:08.973971+00:00
-- url     : https://prove2.me/theorems/0e721990-2d12-434a-bd15-79e6dcd85910
-- title:
--   Theorem 3.1, p. 20 (intermediaries' part) — no tier-t intermediary gains by deviating from (z_{W_{t−1}}, ψ_{W_{t−1}}) after any history
-- statement:
--   This is the intermediaries' half of Theorem 3.1 (the subgame-perfection inequality for tiers $t=1,\dots,n$).
--
--   Consider the symmetric tree with a seller (tier $n+1$), intermediaries in tiers $n,\dots,1$ and buyers (tier $0$), where every tier-$t$ node has $k_t\ge1$ downstream agents. Buyer values are i.i.d. with law $V$: nonnegative, lower support end $0$, finite mean, a continuous strictly positive density, and a strictly increasing virtual value $\phi_V$. Let $W_0=V$ and $W_t=\psi_{W_{t-1}}\big(W_{t-1}^{\mathrm{FH}(k_t)}\big)$ be the anticipated reports (Definition 3.3). Assume Assumption 3.1: for $t=1,\dots,n$, $W_t$ has finite mean, $W_t\mid W_t>0$ has a continuous strictly positive density on its support, and its virtual value is strictly increasing. The equilibrium mechanism of tier $t$ is
--   $$
--   (r_t^*,Y_t^*)=\big(z_{W_{t-1}},\ \psi_{W_{t-1}}\big).
--   $$
--
--   Fix a tier $t\in\{1,\dots,n\}$ and a history $H_t$: mechanisms $(r_s,Y_s)\in\mathcal M$ for the tiers $s=t+1,\dots,n$, the same for all nodes of tier $s$, and a seller reserve $r_S\ge0$. Fix a node $I_{(t,j)}$ and a mechanism $(r,Y)\in\mathcal M$. Suppose all other nodes of tier $t$ and all lower tiers use the equilibrium mechanisms. Then the expected profit of $I_{(t,j)}$ is largest when it uses the equilibrium mechanism:
--   $$
--   \Pi_{(t,j)}\big(H_t;\,(r,Y)\big)\ \le\ \Pi_{(t,j)}\big(H_t;\,(r_t^*,Y_t^*)\big).
--   $$
--
--   Here $\Pi_{(t,j)}=\mathbb E\big[\sum_c (P_c-P_{(t,j)})\mathbf 1\{c\text{ wins}\}\big]$ is display (3). The sum runs over the children $c$ of $I_{(t,j)}$, and the payments $P$ are the minimum winning reports (Definition A.1). Together with the seller's optimal reserve, this is the subgame-perfect-equilibrium property of Theorem 3.1. In the paper it is proved by induction on $t$, from Lemma 2.1(A) (the upstream mechanism acts as a second-price auction) and Lemmas 3.1/B.1 (single-stage optimality of $(z,\psi)$).
--
--   **Formalization Note** The statement is verbatim the intermediaries' component of `IsSPE k n μ (eqMech k μ) (zproj (annLaw k μ n))` in `theorem_3_1`, under the same hypotheses. All readings of the setting definition apply: ties go to the lowest index, a report equal to a reserve wins, payments are minimum winning reports, and a non-integrable profit has value $0$.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), Theorem 3.1, p. 20 (part 1: intermediaries' optimal mechanisms); Definition A.3, p. 44; proof pp. 36–37 ('Intermediaries' Optimal Mechanisms')

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

open MeasureTheory

namespace AdInterm.SPE

theorem theorem_3_1_intermediaries (n : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n →
      RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t)) :
    ∀ t, 1 ≤ t → t ≤ n →
      ∀ h : ℕ → Mechanism, (∀ s, t < s → s ≤ n → IsMech (h s)) →
        ∀ rS : ℝ, 0 ≤ rS →
          ∀ j, j < nodes k n t →
            ∀ m : Mechanism, IsMech m →
              Pi_int k n μ (deviate (eqMech k μ) h t j m) rS t j ≤
                Pi_int k n μ (deviate (eqMech k μ) h t j (eqMech k μ t)) rS t j := by sorry

end AdInterm.SPE
