-- Prove2me | Theorems.Thm_AlgoTransparency_cases_6_8_not_equilibria
-- name    : AlgoTransparency.cases_6_8_not_equilibria
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:54:05.878123+00:00
-- url     : https://prove2.me/theorems/98723d1f-ef4d-434e-8c67-49ecf4362af2
-- title:
--   §4.1, p.18: opaque cases 6–8 are not equilibria (corrected: case 9, both types mixing, can be an equilibrium)
-- statement:
--   Assume the standing assumptions and $0<C_H<C_L$.
--
--   1. No opaque Nash equilibrium has $q_L>0$, $q_H<1$ and ($q_H=0$ or $q_L=1$). This excludes case 6 ($q_H=0$, $q_L=1$), case 7 ($q_H=0$, $0<q_L<1$) and case 8 ($0<q_H<1$, $q_L=1$): L agents never invest in education more eagerly than H agents.
--   2. The paper's further claim that case 9, where both types mix, "cannot be sustained" is false. At $\theta=\tfrac12$, $\lambda=\tfrac45$, $R=1$, $\alpha=\tfrac32$, $\beta=\tfrac{13}{20}$ and $(C_H,C_L)=(\tfrac1{10},\tfrac3{20})$, the profile
--   $$
--   q_H=\tfrac{28}{33},\quad q_L=\tfrac{23}{33},\quad (P_A,P_B,P_C,P_D)=\big(\tfrac{11}{12},1,0,\tfrac16\big)
--   $$
--   is an opaque Nash equilibrium: the firm's margins at $A$ and $D$ vanish and both types are indifferent.
--
--   The surviving equilibria are therefore cases 1–5 and case 9; Lemma 1 decides which of them is selected.
--
--   Differences from the source:
--   - correction: "cases 6 through 9 cannot be sustained in the equilibrium" → cases 6–8 are excluded and clause 2 exhibits a case-9 equilibrium; reason: counterexample at θ = 1/2, λ = 4/5, R = 1, α = 3/2, β = 13/20, (C_H, C_L) = (1/10, 3/20): the stated profile satisfies every equilibrium condition, with the parameters satisfying Assumptions 1–3
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
--   - reading: C_H < C_L, C_H, C_L costs → 0 < C_H < C_L; reason: Figure 1 is the positive quadrant; costs are positive
--   - reading: agents of a type improve "with some probability" → a common mixed strategy q_T ∈ [0,1] per type, with expected masses; reason: p.14: "Agents of the same type use the same strategy"; App. A.1 computes with expected masses
--   - reading: Nash equilibrium (any P_S is a best response at an unoccupied state) → an unoccupied educated state (B, D, F) is hired with probability 1 and an unoccupied uneducated state (A, C, E) with probability 0; reason: every equilibrium written in App. A.1–A.2 uses this rule; without it the payoff-dominance selection has no solution in region N2
--   - encoding: firm optimality via γ^E_S compared with γ_th0, γ_th1 (12) → firm optimality via the signs of the margins m_S at occupied states; reason: same condition when n_S > 0; avoids 0/0 at unoccupied states
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.1, p.18 (PDF 19)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_IsOpaqueEq

namespace AlgoTransparency

/-- **Opaque cases 6–8 are not equilibria; case 9 can be**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §4.1, p.18 (PDF 19), corrected.

1. Under the standing assumptions and `0 < C_H < C_L`, no opaque Nash equilibrium has L agents
   improving with positive probability while H agents do not surely improve and either H agents
   never improve or L agents surely improve: this excludes case 6 (`qH = 0, qL = 1`), case 7
   (`qH = 0, 0 < qL < 1`) and case 8 (`0 < qH < 1, qL = 1`).
2. The paper's further claim that case 9 (both types mixing) "cannot be sustained" is false: at
   `θ = 1/2, λ = 4/5, R = 1, α = 3/2, β = 13/20` and `(C_H, C_L) = (1/10, 3/20)` the profile
   `qH = 28/33, qL = 23/33, P = (P_A, P_B, P_C, P_D) = (11/12, 1, 0, 1/6)` is an opaque Nash
   equilibrium.

**Formalization Note.** Clause 2 is the witness of the correction; these parameters satisfy the
standing assumptions (`Solutions/verification/AlgoTransparency_sanity.lean`). -/
theorem cases_6_8_not_equilibria :
    (∀ p : Params, Standing p → ∀ CH CL : ℝ, 0 < CH → CH < CL →
      ∀ (qH qL : ℝ) (P : OState → ℝ), IsOpaqueEq p CH CL qH qL P →
        ¬ (0 < qL ∧ qH < 1 ∧ (qH = 0 ∨ qL = 1))) ∧
    IsOpaqueEq ⟨1 / 2, 4 / 5, 1, 3 / 2, 13 / 20⟩ (1 / 10) (3 / 20) (28 / 33) (23 / 33)
      (fun S => match S with
        | .A => 11 / 12
        | .B => 1
        | .C => 0
        | .D => 1 / 6) := by sorry

end AlgoTransparency
