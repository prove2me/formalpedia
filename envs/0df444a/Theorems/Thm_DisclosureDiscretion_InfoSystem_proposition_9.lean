-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_9
-- name    : DisclosureDiscretion.InfoSystem.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:32.983662+00:00
-- url     : https://prove2.me/theorems/66ea8e4a-ef28-42c0-baea-b102904dc2f4
-- title:
--   Proposition 9, p. 27 (PDF 29) — the CEO installs N for k ≥ tc̄/2, D for k_2A ≤ k < tc̄/2, P for k < k_2A
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$, and let $k_{2A}=t\bar c[\sqrt{(1-p)(1-pt^2)}-(1-p)]/(p[1-t^2])$. Write $E_N=E[\wp(N,s)]$, $E_P=E[\wp(P,s)]$, and $E_D(x,q)$ for the expected price under the discretionary system at the $D$-subgame profile $(x,q)$.
--
--   1. **Weak union**, $k\ge t\bar c/2$: the CEO installs $N$, i.e.
--   $$E_P<E_N\quad\text{and}\quad E_D(x,q)<E_N\ \text{for every $D$-subgame equilibrium }(x,q).$$
--   2. **Intermediate union**, $k_{2A}\le k<t\bar c/2$: the CEO installs $D$, i.e. there is a $D$-subgame equilibrium $(x,q)$ with $E_D(x,q)>E_N$ and $E_D(x,q)>E_P$; and if moreover $k>k_{2A}$, these two inequalities hold at every $D$-subgame equilibrium.
--   3. **Strong union**, $k<k_{2A}$: the CEO installs $P$, i.e. $E_P>E_N$; there is a $D$-subgame equilibrium $(x,q)$ with $E_D(x,q)<E_P$; and $E_D(x,q)<E_P$ at every $D$-subgame equilibrium with $x>k/t$.
--
--   The optimal information system is thus determined by the union's strength: no information against a weak union, discretion against an intermediate one, and committed public disclosure against a strong one.
--
--   **Formalization Note** The $D$-subgame can have several equilibria near $k_{2A}$, which the paper does not consider. For $\bar c=1$, $t=0.4$, $p=0.8$, $k=k_{2A}-0.001$ there is a mixed equilibrium $(k/t,q\approx0.567)$ with $E_D\approx0.33297>E_P\approx0.31652$; and for $t=p=1/2$, $k=k_{2A}$, the equilibrium $(k/t,1)$ has $E_D<E_P$. Hence the "every equilibrium" reading is stated only where it holds: in part 1, in part 2 for $k>k_{2A}$, and in part 3 for equilibria with $x>k/t$; elsewhere the statement is existential. Under the standing assumption, part 1 is vacuous when $t\ge1/2$, as in the paper.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 27 (PDF 29), Proposition 9; proof p. 40 (PDF 42)

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_9 (cbar t p k : ℝ) (h : Standing cbar t p k) :
    (t * cbar / 2 ≤ k →
      expPriceP cbar t p k < expPriceN cbar t k ∧
      ∀ x q : ℝ, IsDEquilibrium cbar t p k x q →
        expPriceD cbar t p k x q < expPriceN cbar t k) ∧
    (k2A cbar t p ≤ k → k < t * cbar / 2 →
      (∃ x q : ℝ, IsDEquilibrium cbar t p k x q ∧
        expPriceN cbar t k < expPriceD cbar t p k x q ∧
        expPriceP cbar t p k < expPriceD cbar t p k x q) ∧
      (k2A cbar t p < k → ∀ x q : ℝ, IsDEquilibrium cbar t p k x q →
        expPriceN cbar t k < expPriceD cbar t p k x q ∧
        expPriceP cbar t p k < expPriceD cbar t p k x q)) ∧
    (k < k2A cbar t p →
      expPriceN cbar t k < expPriceP cbar t p k ∧
      (∃ x q : ℝ, IsDEquilibrium cbar t p k x q ∧
        expPriceD cbar t p k x q < expPriceP cbar t p k) ∧
      (∀ x q : ℝ, IsDEquilibrium cbar t p k x q → k / t < x →
        expPriceD cbar t p k x q < expPriceP cbar t p k)) := by sorry

end DisclosureDiscretion.InfoSystem
