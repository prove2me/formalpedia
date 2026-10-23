-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_8
-- name    : DisclosureDiscretion.InfoSystem.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:38.626361+00:00
-- url     : https://prove2.me/theorems/e5d97583-b2b1-4048-8fda-bf8db9f2a9a2
-- title:
--   Proposition 8, p. 26 (PDF 28) — discretion optimal requires k < tc̄/2 and c^φ ≤ k/t; sufficient when c^φ < k/t
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$. Say discretionary disclosure is **optimal** at a $D$-subgame equilibrium $(c^\phi,q)$ if $E[\wp(D,s)]>E[\wp(N,s)]$ and $E[\wp(D,s)]>E[\wp(P,s)]$.
--
--   1. (Necessity) For every $D$-subgame equilibrium $(c^\phi,q)$ at which discretion is optimal,
--   $$k<\frac{t\bar c}{2}\quad\text{and}\quad c^\phi\le\frac kt.$$
--   2. (Sufficiency, strict case) If $k<t\bar c/2$, then discretion is optimal at every $D$-subgame equilibrium with $c^\phi<k/t$.
--   3. (Sufficiency, mixed case) If $t\ne1/2$, $(1-p)[1-2t+(1-p)t^2]\ge0$, $k_{2A}\le k\le k_{2B}$ and $k<t\bar c/2$, then discretion is optimal at the equilibrium $(k/t,q_{2C})$ of Proposition 4.
--
--   The union is kept from bargaining under silence exactly when the value of silence does not exceed the bargaining threshold $k/t$.
--
--   **Formalization Note** The paper's sufficiency claim for every equilibrium with $c^\phi=k/t$ is false and is not formalized: just below $k_{2A}$ there are Case 2C equilibria with large mixing probability ($\bar c=1$, $t=0.4$, $p=0.8$, $k=k_{2A}-0.001$, $q\approx0.90$) at which $E[\wp(P,s)]>E[\wp(D,s)]$. Part 3 states sufficiency for the paper's own equilibrium $(k/t,q_{2C})$, under the hypotheses that make the printed $k_{2B}$ defined.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 26 (PDF 28), Proposition 8

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_8 (cbar t p k : ℝ) (h : Standing cbar t p k) :
    (∀ x q : ℝ, IsDEquilibrium cbar t p k x q → DOptimal cbar t p k x q →
      k < t * cbar / 2 ∧ x ≤ k / t) ∧
    (∀ x q : ℝ, k < t * cbar / 2 → IsDEquilibrium cbar t p k x q → x < k / t →
      DOptimal cbar t p k x q) ∧
    (K2BDefined t p → k2A cbar t p ≤ k → k ≤ k2B cbar t p → k < t * cbar / 2 →
      DOptimal cbar t p k (k / t) (q2C cbar t p k)) := by sorry

end DisclosureDiscretion.InfoSystem
