-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_2
-- name    : DisclosureDiscretion.InfoSystem.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:21.859984+00:00
-- url     : https://prove2.me/theorems/255171b9-2af0-43fc-8856-39edd274e4b3
-- title:
--   Proposition 2, p. 17 (PDF 19) — Case 2A: two disclosure intervals with c^φ_2A > k/t for k ∈ [k_1A, k_2A)
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$, and $k_{1A}\le k<k_{2A}$, where $k_{1A}$ is as in Proposition 1 and
--   $$k_{2A}=\frac{t\bar c\,[\sqrt{(1-p)(1-pt^2)}-(1-p)]}{p[1-t^2]}.$$
--   Let
--   $$c^\phi_{2A}=\frac{\sqrt{[(1-p)t\bar c-kp]^2+p[2-t^2][(1-p)(t\bar c)^2-k^2p]}-[(1-p)t\bar c-kp]}{pt[2-t^2]}.$$
--   Then $k/t<c^\phi_{2A}$, $(1-t)c^\phi_{2A}\le k/t$, $c^\phi_{2A}\le\bar c$, the pair $(c^\phi_{2A},1)$ is an equilibrium of the $D$-subgame (the union bargains after silence, priced at $[1-t]c^\phi_{2A}$), and the informed CEO withholds exactly the cash flows in
--   $$[0,(1-t)c^\phi_{2A})\cup(k/t,c^\phi_{2A}),$$
--   so she discloses the intermediate values $[(1-t)c^\phi_{2A},k/t]$ and the upper tail $[c^\phi_{2A},\bar c]$.
--
--   The intermediate bad-news disclosures are made to keep the union from bargaining.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 17 (PDF 19), Proposition 2, equation (2)

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_2 (cbar t p k : ℝ) (h : Standing cbar t p k)
    (hk1 : k1A cbar t p ≤ k) (hk2 : k < k2A cbar t p) :
    k / t < c2Aphi cbar t p k ∧ (1 - t) * c2Aphi cbar t p k ≤ k / t ∧
    c2Aphi cbar t p k ≤ cbar ∧
    IsDEquilibrium cbar t p k (c2Aphi cbar t p k) 1 ∧
    ndSet cbar t k (silencePrice t (c2Aphi cbar t p k) 1) =
      Set.Ico 0 ((1 - t) * c2Aphi cbar t p k) ∪ Set.Ioo (k / t) (c2Aphi cbar t p k) := by sorry

end DisclosureDiscretion.InfoSystem
