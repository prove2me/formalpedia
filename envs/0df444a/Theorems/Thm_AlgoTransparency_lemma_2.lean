-- Prove2me | Theorems.Thm_AlgoTransparency_lemma_2
-- name    : AlgoTransparency.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:51.794189+00:00
-- url     : https://prove2.me/theorems/1ce17395-e4ab-4327-a448-d73d081f229c
-- title:
--   Lemma 2: the transparent equilibrium and the firm's payoff
-- statement:
--   Assume the standing assumptions and $0<C_H<C_L$.
--
--   1. If $R<C_H$, a transparent equilibrium exists, and every one has $q_H=q_L=0$ (case 1) and $\Pi_T=\Pi_{T1}=0$.
--   2. If $C_H<R<C_L$, a transparent equilibrium exists, and every one has $q_H=1$, $q_L=0$ (case 2) and $\Pi_T=\Pi_{T2}=\theta(\alpha+\beta-R)$.
--   3. If $C_L<R$, a transparent equilibrium exists, and every one has $q_H=q_L=1$ (case 3) and $\Pi_T=\Pi_{T3}=\theta(\alpha+\beta)+(1-\theta)\beta-R$.
--
--   This is the transparent half of the payoff comparison in Theorem 1.
--
--   Differences from the source:
--   - reading: "the equilibrium outcome depends on (C_H, C_L) as shown in Figure 3" → existence of a transparent equilibrium and the strategies and payoff of every one, on the open regions R < C_H, C_H < R < C_L, C_L < R; reason: Figure 3 draws these regions; boundaries are not claimed
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
--   - reading: C_H < C_L, C_H, C_L costs → 0 < C_H < C_L; reason: Figure 1 is the positive quadrant; costs are positive
--   - reading: agents of a type improve "with some probability" → a common mixed strategy q_T ∈ [0,1] per type, with expected masses; reason: p.14: "Agents of the same type use the same strategy"; App. A.1 computes with expected masses
--   - reading: Nash equilibrium (any P_S is a best response at an unoccupied state) → an unoccupied educated state (B, D, F) is hired with probability 1 and an unoccupied uneducated state (A, C, E) with probability 0; reason: every equilibrium written in App. A.1–A.2 uses this rule; without it the payoff-dominance selection has no solution in region N2
--   - encoding: firm optimality via γ^E_S compared with γ_th0, γ_th1 (12) → firm optimality via the signs of the margins m_S at occupied states; reason: same condition when n_S > 0; avoids 0/0 at unoccupied states
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, Lemma 2 and Figure 3, pp.20–21 (PDF 21–22); App. A.2, pp.46–48 (PDF 47–49)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_IsTransparentEq
import Definitions.Def_AlgoTransparency_firmPayoffT

namespace AlgoTransparency

/-- **Lemma 2: the transparent equilibrium and the firm's payoff**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, Lemma 2 and Figure 3, pp.20–21 (PDF 21–22), and App. A.2, pp.46–48
(PDF 47–49).

Under the standing assumptions and `0 < C_H < C_L`:

1. if `R < C_H`, a transparent equilibrium exists, and every one is case 1, `qH = qL = 0`, with
   `Π_T = Π_T1 = 0`;
2. if `C_H < R < C_L`, a transparent equilibrium exists, and every one is case 2, `qH = 1,
   qL = 0`, with `Π_T = Π_T2 = θ(α + β − R)`;
3. if `C_L < R`, a transparent equilibrium exists, and every one is case 3, `qH = qL = 1`, with
   `Π_T = Π_T3 = θ(α + β) + (1 − θ)β − R`.

**Formalization Note.** Figure 3 draws the three regions; they are read as the open sets above.
The lemma's "the equilibrium outcome" is formalized as existence plus a statement about every
equilibrium. -/
theorem lemma_2 (p : Params) (hp : Standing p) (CH CL : ℝ) (hCH : 0 < CH) (hHL : CH < CL) :
    (p.R < CH →
      (∃ (qH qL : ℝ) (P : TState → ℝ), IsTransparentEq p CH CL qH qL P) ∧
      ∀ (qH qL : ℝ) (P : TState → ℝ), IsTransparentEq p CH CL qH qL P →
        qH = 0 ∧ qL = 0 ∧ firmPayoffT p qH qL P = 0) ∧
    (CH < p.R ∧ p.R < CL →
      (∃ (qH qL : ℝ) (P : TState → ℝ), IsTransparentEq p CH CL qH qL P) ∧
      ∀ (qH qL : ℝ) (P : TState → ℝ), IsTransparentEq p CH CL qH qL P →
        qH = 1 ∧ qL = 0 ∧ firmPayoffT p qH qL P = p.θ * (p.α + p.β - p.R)) ∧
    (CL < p.R →
      (∃ (qH qL : ℝ) (P : TState → ℝ), IsTransparentEq p CH CL qH qL P) ∧
      ∀ (qH qL : ℝ) (P : TState → ℝ), IsTransparentEq p CH CL qH qL P →
        qH = 1 ∧ qL = 1 ∧ firmPayoffT p qH qL P = p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R) := by sorry

end AlgoTransparency
