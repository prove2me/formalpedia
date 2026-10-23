-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_7_c
-- name    : DisclosureDiscretion.InfoSystem.proposition_7_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:27.460113+00:00
-- url     : https://prove2.me/theorems/fbce6a14-9b5b-49dc-9b56-094a7d80ded4
-- title:
--   Proposition 7(c), p. 25 (PDF 27) — expected stock price under D at the equilibria of Propositions 1–4
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$, and let $c_1^\phi,k_{1A},k_{1B},c^\phi_{2A},k_{2A},c^\phi_{2B},k_{2B},q_{2C}$ be as in Propositions 1–4. The CEO's expected stock price under the discretionary system $D$, evaluated at the equilibria of Propositions 1–4, is:
--
--   1. $[1-t]\bar c/2$ if $k<k_{1A}$ (equilibrium $(c_1^\phi,1)$);
--   2. $\dfrac{t[1-t][\bar c^2-pt(1-t)(c^\phi_{2A})^2]+pk^2}{2t\bar c}$ if $k_{1A}\le k<k_{2A}$ (equilibrium $(c^\phi_{2A},1)$);
--   3. if $k_{2A}\le k\le k_{2B}$ (equilibrium $(k/t,q_{2C})$), with $q=q_{2C}$,
--   $$\frac{[1-(1-p)tq]\bar c}{2}-\frac{p[(1-t)^2t^2\bar c^2-k^2(1-tq)^2]}{2[1-t]^2t\bar c}-\frac{pqk^2[1-tq(2-tq)(2-2t+t^2)]}{2[1-t]^2t\bar c};$$
--   4. $\dfrac{[1-pt][1-t]^2\bar c^2+pt(c^\phi_{2B})^2}{2[1-t]^2\bar c}$ if $k_{2B}<k\le k_{1B}$ (equilibrium $(c^\phi_{2B},0)$);
--   5. $\dfrac{[1-pt]t\bar c^2+pk^2}{2t\bar c}$ if $k>k_{1B}$ (equilibrium $(c_1^\phi,0)$).
--
--   Comparing these with Proposition 7(a)–(b) yields the CEO's choice of information system.
--
--   **Formalization Note** Cases 3 and 4 additionally assume $t\ne1/2$ and $(1-p)[1-2t+(1-p)t^2]\ge0$, where the printed $k_{2B}$ is defined. In the printed case 3 the last numerator reads $pqk^2$ with an unsubscripted $q$; it is $q_{2C}$. The expected price under $D$ is defined in the model from the equilibrium, not by these formulas.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 25 (PDF 27), Proposition 7(c)

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_7_c (cbar t p k : ℝ) (h : Standing cbar t p k) :
    (k < k1A cbar t p →
      expPriceD cbar t p k (c1phi cbar p) 1 = (1 - t) * cbar / 2) ∧
    (k1A cbar t p ≤ k → k < k2A cbar t p →
      expPriceD cbar t p k (c2Aphi cbar t p k) 1 =
        (t * (1 - t) * (cbar ^ 2 - p * t * (1 - t) * c2Aphi cbar t p k ^ 2) + p * k ^ 2) /
          (2 * t * cbar)) ∧
    (K2BDefined t p → k2A cbar t p ≤ k → k ≤ k2B cbar t p →
      expPriceD cbar t p k (k / t) (q2C cbar t p k) =
        (1 - (1 - p) * t * q2C cbar t p k) * cbar / 2 -
          p * ((1 - t) ^ 2 * t ^ 2 * cbar ^ 2 - k ^ 2 * (1 - t * q2C cbar t p k) ^ 2) /
            (2 * (1 - t) ^ 2 * t * cbar) -
          p * q2C cbar t p k * k ^ 2 *
              (1 - t * q2C cbar t p k * (2 - t * q2C cbar t p k) * (2 - 2 * t + t ^ 2)) /
            (2 * (1 - t) ^ 2 * t * cbar)) ∧
    (K2BDefined t p → k2B cbar t p < k → k ≤ k1B cbar t p →
      expPriceD cbar t p k (c2Bphi cbar t p k) 0 =
        ((1 - p * t) * (1 - t) ^ 2 * cbar ^ 2 + p * t * c2Bphi cbar t p k ^ 2) /
          (2 * (1 - t) ^ 2 * cbar)) ∧
    (k1B cbar t p < k →
      expPriceD cbar t p k (c1phi cbar p) 0 =
        ((1 - p * t) * t * cbar ^ 2 + p * k ^ 2) / (2 * t * cbar)) := by sorry

end DisclosureDiscretion.InfoSystem
