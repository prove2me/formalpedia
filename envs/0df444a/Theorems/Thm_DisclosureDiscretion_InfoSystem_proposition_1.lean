-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_1
-- name    : DisclosureDiscretion.InfoSystem.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:31.610642+00:00
-- url     : https://prove2.me/theorems/ea7c1c05-7b84-4ad2-9790-bc8d6543aa0a
-- title:
--   Proposition 1, p. 15 (PDF 17) — single-tailed disclosure in [c₁^φ, c̄] when k < k_1A or k > k_1B
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$, and let
--   $$c_1^\phi=\frac{[\sqrt{1-p}-(1-p)]\,\bar c}{p},\qquad k_{1A}=t[1-t]c_1^\phi,\qquad k_{1B}=\frac{tc_1^\phi}{1-t}.$$
--
--   1. If $k<k_{1A}$, then $c_1^\phi>k/t$, $c_1^\phi\le\bar c$, the pair $(x,q)=(c_1^\phi,1)$ is an equilibrium of the $D$-subgame (the union always bargains after silence, which is priced at $[1-t]c_1^\phi$), and the informed CEO withholds exactly the cash flows in $[0,c_1^\phi)$.
--   2. If $k>k_{1B}$, then $c_1^\phi<k/t$, $c_1^\phi\le\bar c$, the pair $(c_1^\phi,0)$ is an equilibrium of the $D$-subgame (the union does not bargain after silence, which is priced at $c_1^\phi$), and the informed CEO withholds exactly the cash flows in $[0,c_1^\phi)$.
--
--   In both cases disclosure is single-tailed, on $[c_1^\phi,\bar c]$, as in Dye (1985): for extreme bargaining costs the CEO's disclosure ignores the union.
--
--   **Formalization Note** Parts (b) and (c) of the paper (the union's action and the prices after each signal) are encoded by the equilibrium pair $(x,q)$ and by Lemma 2's pricing rule in the model definition.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 15 (PDF 17), Proposition 1, equation (1) p. 14 (PDF 16)

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_1 (cbar t p k : ℝ) (h : Standing cbar t p k) :
    (k < k1A cbar t p →
      k / t < c1phi cbar p ∧ c1phi cbar p ≤ cbar ∧
      IsDEquilibrium cbar t p k (c1phi cbar p) 1 ∧
      ndSet cbar t k (silencePrice t (c1phi cbar p) 1) = Set.Ico 0 (c1phi cbar p)) ∧
    (k1B cbar t p < k →
      c1phi cbar p < k / t ∧ c1phi cbar p ≤ cbar ∧
      IsDEquilibrium cbar t p k (c1phi cbar p) 0 ∧
      ndSet cbar t k (silencePrice t (c1phi cbar p) 0) = Set.Ico 0 (c1phi cbar p)) := by sorry

end DisclosureDiscretion.InfoSystem
