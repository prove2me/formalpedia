-- Prove2me | Theorems.Thm_EquivariantHomogeneous_semidirect_h_function
-- name    : EquivariantHomogeneous.semidirect_h_function
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:33:49.074466+00:00
-- url     : https://prove2.me/theorems/42a9fccd-ad4d-42e2-a2b5-46fb332708c6
-- title:
--   Appendix A.2, Eq. (32): for semidirect products h(x, g) = h(g)
-- statement:
--   Let $G=N\rtimes H$: $N\trianglelefteq G$ is normal, $N\cap H=\{e\}$, and every $g\in G$ is a product $g=nh$ with $n\in N$, $h\in H$. Then there is a section $s$ of $G\to G/H$ with $s(H)=e$ taking values in $N$. For every such section:
--
--   1. $s(nH)=n$ for all $n\in N$;
--   2. $s(nx)=n\,s(x)$ for all $n\in N$, $x\in G/H$;
--   3. the $\mathrm h$-function does not depend on its first argument:
--   $$\mathrm h(x,g)=\mathrm h(g)\qquad\text{for all }x\in G/H,\ g\in G\quad\text{(eq. (32))};$$
--   4. $\mathrm h(n)=e$ for $n\in N$.
--
--   Item 4 is why the $\rho_1$ factor in the twisted cross-correlation (14) disappears for semidirect products (Section 3.2), and item 3 is the simplification used for $\mathrm{SE}(3)$ in Section 6.2.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Appendix A.2, Eqs. (31)-(32), p. 15; used in Section 3.2, p. 7 and Section 6.2, p. 9

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem semidirect_h_function {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
    (hNH : N ⊓ H = ⊥) (hNHG : ∀ g : G, ∃ n ∈ N, ∃ h ∈ H, g = n * h) :
    (∃ s : CosetSection H, ∀ x, s.toFun x ∈ N) ∧
    ∀ s : CosetSection H, (∀ x, s.toFun x ∈ N) →
      (∀ n ∈ N, s.toFun (QuotientGroup.mk n) = n) ∧
      (∀ n ∈ N, ∀ x : G ⧸ H, s.toFun (n • x) = n * s.toFun x) ∧
      (∀ (x : G ⧸ H) (g : G), hfun s x g = hElem s g) ∧
      (∀ n ∈ N, hElem s n = 1) := by sorry

end EquivariantHomogeneous
