-- Prove2me | Theorems.Thm_BellDetEff_TwoParty_eq_15
-- name    : BellDetEff.TwoParty.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:05.572178+00:00
-- url     : https://prove2.me/theorems/a745c16d-d7cb-435e-bd19-3c2447e1574e
-- title:
--   Eq. (15) — the witness box under efficiency η has Bell value η²(M_A M_B − 1) − η(M_A + M_B − 2)
-- statement:
--   Let $P$ be a prime and $M_A,M_B$ integers with $1\le M_A\le P$ and $1\le M_B\le P$. Let $p^{NS}$ be the box of eq. (13) and $p^{NS}_\eta$ the corresponding behaviour under detector efficiency $\eta$ (eq. (2)). Then for every real $\eta$, the Bell expression (6) evaluates to
--   $$I_{M_AM_B(P+1)(P+1)}(p^{NS}_\eta)=\eta^2(M_AM_B-1)-\eta(M_A+M_B-2).$$
--
--   Since the expression is at most $0$ for every local hidden variable model, $p^{NS}_\eta$ cannot be simulated locally as soon as this value is positive, i.e. for $\eta>(M_A+M_B-2)/(M_AM_B-1)$; this is how the paper concludes Theorem 2.
--
--   **Formalization Note** The identity is polynomial in $\eta$ and is stated for every real $\eta$. The hypotheses $M_A,M_B\le P$ are not needed for the identity and are kept for uniformity with the other results; $M_A,M_B\ge 1$ is needed for the count $M_AM_B-1$.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, p. 3, proof of Theorem 2, eq. (15)

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Efficiency
import Definitions.Def_BellDetEff_TwoParty_BellInequality

namespace BellDetEff.TwoParty

/-- Eq. (15), proof of Theorem 2 (Cao–Peng, arXiv:1607.04350v1, p. 3): the Bell value (6) of the
witness behaviour (13) under detector efficiency `η`, for a prime `P` and `1 ≤ MA, MB ≤ P`, is `η²(MA MB − 1) − η(MA + MB − 2)`. -/
theorem eq_15 (P MA MB : ℕ) [Fact P.Prime] (hA : 1 ≤ MA) (hB : 1 ≤ MB) (hAP : MA ≤ P)
    (hBP : MB ≤ P) (η : ℝ) :
    bellValue P (withEff (witnessBox P MA MB) η) =
      η ^ 2 * ((MA : ℝ) * MB - 1) - η * ((MA : ℝ) + MB - 2) := by sorry

end BellDetEff.TwoParty
