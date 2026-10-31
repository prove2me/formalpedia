-- Prove2me | Theorems.Thm_AlgoTransparency_theorem_1
-- name    : AlgoTransparency.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:54:51.828617+00:00
-- url     : https://prove2.me/theorems/df5c1910-b358-4e7b-aa66-0380489a3d26
-- title:
--   Theorem 1 (corrected: N3/C3 clauses hold only where $\lambda C_H<(1-\lambda)C_L$; the $\beta_2$ clause covers $C_L<\lambda R$, $\lambda C_H>(1-\lambda)C_L$)
-- statement:
--   Assume the standing assumptions ($0<\theta<1$, $\tfrac12\le\lambda\le1$, Assumptions 1–3) and education costs $0<C_H<C_L$. Compare the firm's payoff $\Pi_O$ at any selected (payoff-dominant) opaque outcome with its payoff $\Pi_T$ at any transparent Nash equilibrium.
--
--   1. **Existence.** If $(C_H,C_L)$ lies in one of the regions $N_1,N_2,C_4,C_1,C_2',N_3',C_3'$, and $\lambda<1$ or $R<C_L$, then a selected opaque outcome and a transparent equilibrium exist.
--   2. On $N_1$, $N_2$, $N_3'$ and $C_3'$, transparency is never strictly better: $\Pi_T\le\Pi_O$.
--   3. On $C_1$: $\Pi_O<\Pi_T\iff\beta>\beta_1$.
--   4. On $C_2'$: $\Pi_O<\Pi_T\iff\beta>\beta_2$.
--   5. On $C_4$: $\Pi_O<\Pi_T$.
--
--   Here $\beta_1=\lambda\theta(\alpha-R)-(1-\lambda)(1-\theta)R+R-\theta\alpha$ and $\beta_2=R-\dfrac{\alpha R(1-\lambda)}{(\alpha-R)\lambda+R(1-\lambda)}$, and the regions are
--   $N_1$: $R<C_H$; $N_2$: $C_H<(1-\lambda)R<R<C_L$; $C_4$: $(1-\lambda)R<C_H<R<C_L$; $C_1$: $(1-\lambda)R<C_H$, $\lambda R<C_L<R$; $C_2'$: $C_L<\lambda R$, $(1-\lambda)C_L<\lambda C_H$; $N_3'$: $C_L<(1-\lambda)R$, $\lambda C_H<(1-\lambda)C_L$; $C_3'$: $(1-\lambda)R<C_L<R$, $\lambda C_H<(1-\lambda)C_L$.
--
--   At $\lambda=1$ the opaque game has no equilibrium on $C_2'$, so clause 4 is vacuous there and clause 1 claims no existence there.
--
--   The theorem identifies when hiding a correlational feature from strategic agents costs the firm: transparency pays when it makes agents separate on education ($C_4$), or when education is productive enough ($C_1$, $C_2'$).
--
--   Differences from the source:
--   - correction: regions N3, C3 ("never strictly better", "never prefer") and C2 ("prefer to be transparent if β > β2") of Figure 4 → regions N3', C3' and C2', whose shared boundary is the ray λC_H = (1 − λ)C_L instead of the line C_H = (1 − λ)R; reason: at θ = 1/2, λ = 4/5, R = 1, α = 3/2, β = 13/20, (C_H, C_L) = (1/10, 3/20), a point of the printed N3 satisfying Assumptions 1–3, the selected opaque outcome is a both-types-mixing equilibrium with Π_O = 161/440, while the unique transparent equilibrium gives Π_T = 2/5 > 161/440; the same happens in the printed C3 at (1/10, 7/20)
--   - generalization: "the firm will prefer to be transparent if β > β1" (C1) and "if β > β2" (C2) → Π_O < Π_T iff β > β1, and iff β > β2; reason: (13) and (14) state iff; the converse is the paper's own computation; specializes to the printed "if"
--   - generalization: no existence claim → existence of a selected opaque outcome and a transparent equilibrium on every region when λ < 1 or R < C_L; reason: makes the comparison clauses non-vacuous; Lemmas 1–2 assert it implicitly; at λ = 1 and C_L < R no opaque equilibrium exists
--   - reading: "the firm prefers to be transparent" / "transparent is never strictly better" → Π_O < Π_T / Π_T ≤ Π_O; reason: the firm compares its payoffs (§4.3)
--   - reading: the regions of Figure 4 → open sets of inequalities read off the figure, intersected with 0 < C_H < C_L; reason: the paper defines the regions only by the figure and claims no boundary
--   - reading: "the equilibrium outcome that maximizes the utilities for both agent types" (p.19) → IsOpaqueOutcome: an opaque equilibrium whose per-agent H and L utilities are each ≥ those of every opaque equilibrium; reason: the paper's payoff-dominance rule, applied against all equilibria rather than its list of five cases
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
--   - reading: C_H < C_L, C_H, C_L costs → 0 < C_H < C_L; reason: Figure 1 is the positive quadrant; costs are positive
--   - reading: agents of a type improve "with some probability" → a common mixed strategy q_T ∈ [0,1] per type, with expected masses; reason: p.14: "Agents of the same type use the same strategy"; App. A.1 computes with expected masses
--   - reading: Nash equilibrium (any P_S is a best response at an unoccupied state) → an unoccupied educated state (B, D, F) is hired with probability 1 and an unoccupied uneducated state (A, C, E) with probability 0; reason: every equilibrium written in App. A.1–A.2 uses this rule; without it the payoff-dominance selection has no solution in region N2
--   - encoding: firm optimality via γ^E_S compared with γ_th0, γ_th1 (12) → firm optimality via the signs of the margins m_S at occupied states; reason: same condition when n_S > 0; avoids 0/0 at unoccupied states
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, Theorem 1, p.26 (PDF 27); regions from Figure 4, p.21 (PDF 22)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_IsOpaqueOutcome
import Definitions.Def_AlgoTransparency_IsTransparentEq
import Definitions.Def_AlgoTransparency_firmPayoffO
import Definitions.Def_AlgoTransparency_firmPayoffT
import Definitions.Def_AlgoTransparency_InRegion
import Definitions.Def_AlgoTransparency_beta1
import Definitions.Def_AlgoTransparency_beta2

namespace AlgoTransparency

/-- **Theorem 1 (corrected): when the firm prefers a transparent algorithm**, Wang, Huang, Jasin &
Singh, arXiv:2008.09283v1, Theorem 1, p.26 (PDF 27).

Assume the standing assumptions (`0 < θ < 1`, `1/2 ≤ λ ≤ 1`, Assumptions 1–3) and costs
`0 < C_H < C_L`. Compare the firm's payoff `Π_O` at any selected opaque outcome
(`IsOpaqueOutcome`) with its payoff `Π_T` at any transparent Nash equilibrium
(`IsTransparentEq`).

1. **Existence.** If `(C_H, C_L)` lies in one of the regions `N1, N2, C4, C1, C2', N3', C3'`, and
   `λ < 1` or `R < C_L`, then a selected opaque outcome and a transparent equilibrium exist.
2. On `N1`, `N2`, `N3'`, `C3'`: `Π_T ≤ Π_O` (transparency is never strictly better).
3. On `C1`: `Π_O < Π_T` iff `β > β1`.
4. On `C2'`: `Π_O < Π_T` iff `β > β2`.
5. On `C4`: `Π_O < Π_T`.

**Formalization Note.** The printed theorem uses the regions N3, C3, C2 of Figure 4; its N3 and C3
clauses are false where `λ C_H > (1 − λ) C_L` (counterexample `θ = 1/2, λ = 4/5, R = 1, α = 3/2,
β = 13/20, (C_H, C_L) = (1/10, 3/20)`: the selected opaque payoff is `161/440 < 2/5 = Π_T`). The
corrected regions `N3'`, `C3'`, `C2'` (`InRegion`) move that part into `C2'`, where the printed C2
clause holds. The paper's "if" in the C1 and C2 clauses is stated as "iff", as in (13)–(14). At
`λ = 1` there is no opaque equilibrium on `C2'`, so clause 4 is vacuous there and clause 1 does
not claim existence. -/
theorem theorem_1 (p : Params) (hp : Standing p) (CH CL : ℝ) (hCH : 0 < CH) (hHL : CH < CL) :
    ((∃ r : Region, InRegion p CH CL r) → (p.lam < 1 ∨ p.R < CL) →
      (∃ (qH qL : ℝ) (P : OState → ℝ), IsOpaqueOutcome p CH CL qH qL P) ∧
      (∃ (qH qL : ℝ) (P : TState → ℝ), IsTransparentEq p CH CL qH qL P)) ∧
    ((InRegion p CH CL .N1 ∨ InRegion p CH CL .N2 ∨ InRegion p CH CL .N3' ∨
        InRegion p CH CL .C3') →
      ∀ (qH qL : ℝ) (P : OState → ℝ) (qH' qL' : ℝ) (P' : TState → ℝ),
        IsOpaqueOutcome p CH CL qH qL P → IsTransparentEq p CH CL qH' qL' P' →
          firmPayoffT p qH' qL' P' ≤ firmPayoffO p qH qL P) ∧
    (InRegion p CH CL .C1 →
      ∀ (qH qL : ℝ) (P : OState → ℝ) (qH' qL' : ℝ) (P' : TState → ℝ),
        IsOpaqueOutcome p CH CL qH qL P → IsTransparentEq p CH CL qH' qL' P' →
          (firmPayoffO p qH qL P < firmPayoffT p qH' qL' P' ↔ beta1 p < p.β)) ∧
    (InRegion p CH CL .C2' →
      ∀ (qH qL : ℝ) (P : OState → ℝ) (qH' qL' : ℝ) (P' : TState → ℝ),
        IsOpaqueOutcome p CH CL qH qL P → IsTransparentEq p CH CL qH' qL' P' →
          (firmPayoffO p qH qL P < firmPayoffT p qH' qL' P' ↔ beta2 p < p.β)) ∧
    (InRegion p CH CL .C4 →
      ∀ (qH qL : ℝ) (P : OState → ℝ) (qH' qL' : ℝ) (P' : TState → ℝ),
        IsOpaqueOutcome p CH CL qH qL P → IsTransparentEq p CH CL qH' qL' P' →
          firmPayoffO p qH qL P < firmPayoffT p qH' qL' P') := by sorry

end AlgoTransparency
