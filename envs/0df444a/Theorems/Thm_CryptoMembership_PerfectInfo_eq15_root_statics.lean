-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_eq15_root_statics
-- name    : CryptoMembership.PerfectInfo.eq15_root_statics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:10.693163+00:00
-- url     : https://prove2.me/theorems/8e72c9b6-bd8e-48af-a25d-1ed1432cada3
-- title:
--   A.2, p. 34 (PDF 35) — raising A or ξ lowers the RHS of (15); the lower root s̲ then falls and the upper root s̄ rises
-- statement:
--   Under the standing assumptions, let $L$ be the left-hand side of (15) and $\mathrm{RHS}(A,\xi)$ its right-hand side.
--
--   1. $\mathrm{RHS}(A,\xi)$ is strictly decreasing in $A+\xi$: if $A+\xi<A'+\xi'$ then $\mathrm{RHS}(A',\xi')<\mathrm{RHS}(A,\xi)$.
--   2. Let $\hat s$ be any maximizer of $L$ and $0<R'<R$. If $L(s)=R$ and $L(s')=R'$ with $s,s'\le\hat s$, then $s'<s$ (the lower root $\underline s$ decreases as the level falls).
--   3. If $L(s)=R$ and $L(s')=R'$ with $s,s'\ge\hat s$, then $s<s'$ (the upper root $\bar s$ increases as the level falls).
--
--   Through $s=A^*-A$, the lower root is the high-price equilibrium and the upper root the low-price equilibrium, so these are the comparative statics behind Proposition 2, part 3.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), A.2, p. 34 (PDF 35)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem eq15_root_statics (P : Params) (hP : P.Standing) :
    (∀ A xi A' xi' : ℝ, A + xi < A' + xi' → rhs15 P A' xi' < rhs15 P A xi) ∧
    ∀ sHat : ℝ, (∀ t : ℝ, lhs15 P t ≤ lhs15 P sHat) →
      (∀ R R' s s' : ℝ, 0 < R' → R' < R → lhs15 P s = R → lhs15 P s' = R' →
          s ≤ sHat → s' ≤ sHat → s' < s) ∧
      (∀ R R' s s' : ℝ, 0 < R' → R' < R → lhs15 P s = R → lhs15 P s' = R' →
          sHat ≤ s → sHat ≤ s' → s < s') := by sorry

end CryptoMembership.PerfectInfo
