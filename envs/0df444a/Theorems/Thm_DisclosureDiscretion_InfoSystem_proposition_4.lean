-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_4
-- name    : DisclosureDiscretion.InfoSystem.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:28.912359+00:00
-- url     : https://prove2.me/theorems/77bc1a85-4ab4-4ce6-811f-82d075655ce4
-- title:
--   Proposition 4, pp. 21–22 (PDF 23–24) — Case 2C: the union mixes with probability q_2C ∈ [0,1) and c^φ = k/t for k ∈ [k_2A, k_2B]
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$; assume that $t\ne1/2$ and $(1-p)[1-2t+(1-p)t^2]\ge0$; and let $k_{2A}\le k\le k_{2B}$ (Propositions 2 and 3). Let
--   $$q_{2C}=\frac{1}{2[1-t]+t^2}\Big(1-\frac{1-t}{tk}\sqrt{2[1-t]k^2+t\bar c[2k-t\bar c][2(1-t)+t^2][1-p]/p}\Big).$$
--   Then $0\le q_{2C}<1$, $\frac{1-tq_{2C}}{1-t}\cdot\frac kt\le\bar c$, the pair $(x,q)=(k/t,q_{2C})$ is an equilibrium of the $D$-subgame (the market values silence at $c^\phi_{2C}=k/t$, the union bargains after silence with probability $q_{2C}$, and silence is priced at $[1-tq_{2C}]k/t$), and the informed CEO withholds exactly the cash flows in
--   $$\Big[0,(1-tq_{2C})\tfrac kt\Big)\cup\Big(\tfrac kt,\tfrac{1-tq_{2C}}{1-t}\cdot\tfrac kt\Big).$$
--
--   This is the mixed-strategy case between Cases 2A and 2B.
--
--   **Formalization Note** Part (c) of the printed proposition gives $\wp(D,\phi)=k/t$; by Lemma 2 and the text on p. 20 the silence price is $[1-tq_{2C}]k/t$ and $k/t$ is the value of silence $c^\phi_{2C}$. The statement formalizes the equilibrium $(k/t,q_{2C})$, which carries the correct price. The hypotheses on $t$ and $p$ are those under which the printed $k_{2B}$ is defined (see Proposition 3).
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), pp. 21–22 (PDF 23–24), Proposition 4, equation (4)

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_4 (cbar t p k : ℝ) (h : Standing cbar t p k) (hg : K2BDefined t p)
    (hk1 : k2A cbar t p ≤ k) (hk2 : k ≤ k2B cbar t p) :
    0 ≤ q2C cbar t p k ∧ q2C cbar t p k < 1 ∧
    (1 - t * q2C cbar t p k) / (1 - t) * (k / t) ≤ cbar ∧
    IsDEquilibrium cbar t p k (k / t) (q2C cbar t p k) ∧
    ndSet cbar t k (silencePrice t (k / t) (q2C cbar t p k)) =
      Set.Ico 0 ((1 - t * q2C cbar t p k) * (k / t)) ∪
        Set.Ioo (k / t) ((1 - t * q2C cbar t p k) / (1 - t) * (k / t)) := by sorry

end DisclosureDiscretion.InfoSystem
