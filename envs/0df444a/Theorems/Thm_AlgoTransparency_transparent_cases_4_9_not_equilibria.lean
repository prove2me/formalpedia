-- Prove2me | Theorems.Thm_AlgoTransparency_transparent_cases_4_9_not_equilibria
-- name    : AlgoTransparency.transparent_cases_4_9_not_equilibria
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:51.103965+00:00
-- url     : https://prove2.me/theorems/6e20b2b3-25df-474f-a8f6-59f27c06a98f
-- title:
--   §4.2, p.20: transparent cases 4–9 are not equilibria (corrected: off the lines $C_H=R$, $C_L=R$)
-- statement:
--   Assume the standing assumptions, $0<C_H<C_L$, $C_H\neq R$ and $C_L\neq R$. Then every transparent Nash equilibrium is one of
--
--   1. case 1: $q_H=q_L=0$;
--   2. case 2: $q_H=1$, $q_L=0$;
--   3. case 3: $q_H=q_L=1$.
--
--   So in the transparent game no type mixes and L agents never out-invest H agents.
--
--   Differences from the source:
--   - correction: cases 4–9 cannot be sustained, for every (C_H, C_L) → only off the lines C_H = R and C_L = R; reason: at C_H = R < C_L the profile q_H = 1/2, q_L = 0, P = (P_E, P_F) = (0, 1) is a transparent equilibrium (case 4 with P_E = 0, which App. A.2 does not consider); at C_L = R the profile q_H = 1, 0 < q_L < 1, P = (0, 1) is a case-5 equilibrium
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
--   - reading: C_H < C_L, C_H, C_L costs → 0 < C_H < C_L; reason: Figure 1 is the positive quadrant; costs are positive
--   - reading: agents of a type improve "with some probability" → a common mixed strategy q_T ∈ [0,1] per type, with expected masses; reason: p.14: "Agents of the same type use the same strategy"; App. A.1 computes with expected masses
--   - reading: Nash equilibrium (any P_S is a best response at an unoccupied state) → an unoccupied educated state (B, D, F) is hired with probability 1 and an unoccupied uneducated state (A, C, E) with probability 0; reason: every equilibrium written in App. A.1–A.2 uses this rule; without it the payoff-dominance selection has no solution in region N2
--   - encoding: firm optimality via γ^E_S compared with γ_th0, γ_th1 (12) → firm optimality via the signs of the margins m_S at occupied states; reason: same condition when n_S > 0; avoids 0/0 at unoccupied states
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.2, p.20 (PDF 21); App. A.2, pp.48–50 (PDF 49–51)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_IsTransparentEq

namespace AlgoTransparency

/-- **Transparent cases 4–9 are not equilibria**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §4.2, p.20 (PDF 21), and App. A.2, pp.48–50 (PDF 49–51), corrected at two
boundary lines.

Under the standing assumptions, `0 < C_H < C_L`, `C_H ≠ R` and `C_L ≠ R`, every transparent Nash
equilibrium is case 1 (`qH = qL = 0`), case 2 (`qH = 1, qL = 0`) or case 3 (`qH = qL = 1`).

**Formalization Note.** The exclusions `C_H ≠ R`, `C_L ≠ R` are needed: at `C_H = R < C_L` the
profile `qH = 1/2, qL = 0, P_E = 0, P_F = 1` is a transparent equilibrium (an H agent gets `0`
either way), a case 4 that App. A.2 misses because it assumes `P_E > 0` there; at `C_L = R`
symmetrically `qH = 1`, `0 < qL < 1`, `P = (0, 1)` is a case-5 equilibrium. Off these two lines
the paper's claim holds as printed. -/
theorem transparent_cases_4_9_not_equilibria (p : Params) (hp : Standing p) (CH CL : ℝ)
    (hCH : 0 < CH) (hHL : CH < CL) (hHR : CH ≠ p.R) (hLR : CL ≠ p.R)
    (qH qL : ℝ) (P : TState → ℝ) (h : IsTransparentEq p CH CL qH qL P) :
    (qH = 0 ∧ qL = 0) ∨ (qH = 1 ∧ qL = 0) ∨ (qH = 1 ∧ qL = 1) := by sorry

end AlgoTransparency
