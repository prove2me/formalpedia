-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_3
-- name    : DisclosureDiscretion.InfoSystem.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:47.678397+00:00
-- url     : https://prove2.me/theorems/22a6e721-e16c-4edd-9781-dfce8b19115e
-- title:
--   Proposition 3, p. 19 (PDF 21) — Case 2B: two disclosure intervals with c^φ_2B < k/t for k ∈ (k_2B, k_1B]
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$; assume that $t\ne1/2$ and $(1-p)[1-2t+(1-p)t^2]\ge0$; and let $k_{2B}<k\le k_{1B}$, where $k_{1B}$ is as in Proposition 1 and
--   $$k_{2B}=\min\Big\{\frac{t[1-t]\bar c\,[\sqrt{[1-p][1-2t+(1-p)t^2]}-(1-p)(1-t)]}{p[1-2t]},\;k_{1B}\Big\}.$$
--   Let
--   $$c^\phi_{2B}=\frac{1-t}{pt[2-4t+t^2]}\Big(\sqrt{[1-t]^2[(1-p)t\bar c-kp]^2+p[2-4t+t^2][(1-p)(t\bar c)^2-k^2p]}-[1-t][(1-p)t\bar c-kp]\Big).$$
--   Then $0\le c^\phi_{2B}<k/t\le c^\phi_{2B}/(1-t)\le\bar c$, the pair $(c^\phi_{2B},0)$ is an equilibrium of the $D$-subgame (the union does not bargain after silence, priced at $c^\phi_{2B}$), and the informed CEO withholds exactly the cash flows in
--   $$[0,c^\phi_{2B})\cup(k/t,\,c^\phi_{2B}/(1-t)),$$
--   so she discloses $[c^\phi_{2B},k/t]$ and $[c^\phi_{2B}/(1-t),\bar c]$.
--
--   Here silence keeps the union away, and the CEO withholds good news just above the bargaining threshold.
--
--   **Formalization Note** The first term of the printed $k_{2B}$ is undefined at $t=1/2$ and where $(1-p)[1-2t+(1-p)t^2]<0$; the two added hypotheses restrict the statement to the parameters where the printed formula is meaningful, and no value is invented outside them.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 19 (PDF 21), Proposition 3, equation (3)

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_3 (cbar t p k : ℝ) (h : Standing cbar t p k) (hg : K2BDefined t p)
    (hk1 : k2B cbar t p < k) (hk2 : k ≤ k1B cbar t p) :
    0 ≤ c2Bphi cbar t p k ∧ c2Bphi cbar t p k < k / t ∧
    k / t ≤ c2Bphi cbar t p k / (1 - t) ∧ c2Bphi cbar t p k / (1 - t) ≤ cbar ∧
    IsDEquilibrium cbar t p k (c2Bphi cbar t p k) 0 ∧
    ndSet cbar t k (silencePrice t (c2Bphi cbar t p k) 0) =
      Set.Ico 0 (c2Bphi cbar t p k) ∪ Set.Ioo (k / t) (c2Bphi cbar t p k / (1 - t)) := by sorry

end DisclosureDiscretion.InfoSystem
