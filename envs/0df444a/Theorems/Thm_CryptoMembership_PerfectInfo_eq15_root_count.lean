-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_eq15_root_count
-- name    : CryptoMembership.PerfectInfo.eq15_root_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:55.261166+00:00
-- url     : https://prove2.me/theorems/d9cea5a6-07b4-4a9d-948d-286074eb4056
-- title:
--   A.2, p. 34 (PDF 35) — (15) has two, one or no roots as its RHS is below, at or above the peak of its LHS
-- statement:
--   Under the standing assumptions, let $L$ be the left-hand side of (15). There is a point $\hat s$ at which $L$ attains its maximum, and for every level $R>0$ the number of solutions of $L(s)=R$ is
--   $$\#\{s: L(s)=R\}=\begin{cases}2 & \text{if } R<L(\hat s),\\ 1 & \text{if } R=L(\hat s),\\ 0 & \text{if } R>L(\hat s).\end{cases}$$
--
--   Since the right-hand side of (15) is a positive constant in $s$, this is the precise content of "generically two cutoff equilibria".
--
--   **Formalization Note** The count is the extended cardinality `Set.encard`, so an infinite solution set would not count as $0$, $1$ or $2$.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), A.2, p. 34 (PDF 35)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem eq15_root_count (P : Params) (hP : P.Standing) :
    ∃ sHat : ℝ, (∀ s : ℝ, lhs15 P s ≤ lhs15 P sHat) ∧
      ∀ R : ℝ, 0 < R →
        ({s : ℝ | lhs15 P s = R}.encard = 2 ↔ R < lhs15 P sHat) ∧
        ({s : ℝ | lhs15 P s = R}.encard = 1 ↔ R = lhs15 P sHat) ∧
        ({s : ℝ | lhs15 P s = R}.encard = 0 ↔ lhs15 P sHat < R) := by sorry

end CryptoMembership.PerfectInfo
