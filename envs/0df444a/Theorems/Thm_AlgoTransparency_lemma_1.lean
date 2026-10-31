-- Prove2me | Theorems.Thm_AlgoTransparency_lemma_1
-- name    : AlgoTransparency.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:54:29.244366+00:00
-- url     : https://prove2.me/theorems/7ee9eba0-c32c-4b26-8162-cca30dcbb770
-- title:
--   Lemma 1 (corrected: case 4 is never selected; case 9 is selected on $C_2'$)
-- statement:
--   Assume the standing assumptions and $0<C_H<C_L$.
--
--   1. **Existence.** If $(C_H,C_L)$ lies in one of the regions $N_1,N_2,C_4,C_1,C_2',N_3',C_3'$, and $\lambda<1$ or $R<C_L$, a selected opaque outcome exists.
--   2. **Characterization.** Every selected opaque outcome $(q_H,q_L,P)$ has the following strategies and firm payoff $\Pi_O$:
--      - on $N_1$, $C_1$, $C_4$: $q_H=q_L=0$ (case 1) and $\Pi_O=\Pi_{O1}=\lambda\theta\alpha-(\lambda\theta+(1-\lambda)(1-\theta))R$;
--      - on $N_2$: $q_H=1$, $q_L=0$ (case 2) and $\Pi_O=\Pi_{O2}=\theta(\alpha+\beta)-\theta R$;
--      - on $N_3'$: $q_H=q_L=1$ (case 3) and $\Pi_O=\Pi_{O3}=\lambda\theta(\alpha+\beta)+(1-\lambda)(1-\theta)\beta-(\lambda\theta+(1-\lambda)(1-\theta))R$;
--      - on $C_3'$: $q_H=1$, $q_L=p_L=\dfrac{\alpha\theta(1-\lambda)-(R-\beta)\theta(1-\lambda)}{(1-\theta)\lambda(R-\beta)}$ (case 5, eq. (A.4)) and $\Pi_O=\Pi_{O5}=\dfrac{2\lambda-1}{\lambda}\,\theta(\alpha+\beta-R)$;
--      - on $C_2'$: both types mix, $0<q_H<1$ and $0<q_L<1$ (case 9), and
--   $$
--   \Pi_O=\Pi_{O9}=\frac{(R-\beta)(2\lambda-1)(\alpha+\beta-R)\big(\lambda\theta(\alpha-R)-(1-\theta)(1-\lambda)R\big)}{R(2\lambda-1)(\alpha+\beta-R)-\alpha\beta\lambda^2}.
--   $$
--
--   At $\lambda=1$ the opaque game has no equilibrium on $C_2'$, so the $C_2'$ part of clause 2 is vacuous there and clause 1 claims nothing there.
--
--   This is the opaque half of the payoff comparison in Theorem 1.
--
--   Differences from the source:
--   - correction: case 4 (payoff Π_O4) is the outcome on a triangle of region C2, and case 9 is never an equilibrium → case 4 is never selected; on C2' the selected outcome is case 9 with payoff Π_O9; Π_O4 is not stated; reason: App. A.1's case-4 range (R − C_H)/(R − C_L) ≤ λ/(1 − λ) reverses the inequality its own condition gives: at θ = 1/2, λ = 4/5, R = 1, α = 3/2, (C_H, C_L) = (3/10, 3/5) the case-4 profile P = (7/8, 1, 0, 1) is not an equilibrium; and at θ = 1/2, λ = 4/5, R = 1, α = 3/2, β = 13/20, (C_H, C_L) = (1/10, 3/20) the case-9 equilibrium is selected
--   - correction: the regions of Figure 2 (and of Figure 4: N3, C3, C2) → the corrected regions N3', C3', C2' of InRegion, whose boundary is the ray λC_H = (1 − λ)C_L; reason: case 9 is selected exactly where λC_H > (1 − λ)C_L and C_L < λR
--   - correction: an equilibrium outcome for every (C_H, C_L) and λ ∈ [1/2, 1] → existence only when λ < 1 or R < C_L; reason: at λ = 1 and C_L < R there is no opaque equilibrium under the off-path convention: D is hired iff unoccupied, so L agents can neither all abstain nor some improve
--   - reading: "the equilibrium outcome depends on (C_H, C_L) as shown in Figure 2" → existence of a selected outcome, and strategies and payoff of every selected outcome, on open regions; reason: the paper names one outcome per region; open sets because Figure 2 claims no boundary
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
--   - reading: C_H < C_L, C_H, C_L costs → 0 < C_H < C_L; reason: Figure 1 is the positive quadrant; costs are positive
--   - reading: agents of a type improve "with some probability" → a common mixed strategy q_T ∈ [0,1] per type, with expected masses; reason: p.14: "Agents of the same type use the same strategy"; App. A.1 computes with expected masses
--   - reading: Nash equilibrium (any P_S is a best response at an unoccupied state) → an unoccupied educated state (B, D, F) is hired with probability 1 and an unoccupied uneducated state (A, C, E) with probability 0; reason: every equilibrium written in App. A.1–A.2 uses this rule; without it the payoff-dominance selection has no solution in region N2
--   - encoding: firm optimality via γ^E_S compared with γ_th0, γ_th1 (12) → firm optimality via the signs of the margins m_S at occupied states; reason: same condition when n_S > 0; avoids 0/0 at unoccupied states
--   - reading: "the equilibrium outcome that maximizes the utilities for both agent types" (p.19) → IsOpaqueOutcome: an opaque equilibrium whose per-agent H and L utilities are each ≥ those of every opaque equilibrium; reason: the paper's payoff-dominance rule, applied against all equilibria rather than its list of five cases
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, Lemma 1, p.18 (PDF 19); App. A.1, pp.39–46 (PDF 40–47), eq. (A.4)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_IsOpaqueOutcome
import Definitions.Def_AlgoTransparency_firmPayoffO
import Definitions.Def_AlgoTransparency_InRegion

namespace AlgoTransparency

/-- **Lemma 1 (corrected): the selected opaque outcome and the firm's payoff**, Wang, Huang,
Jasin & Singh, arXiv:2008.09283v1, Lemma 1, p.18 (PDF 19), and App. A.1, pp.39–46 (PDF 40–47).

Assume the standing assumptions and `0 < C_H < C_L`.

1. **Existence.** If `(C_H, C_L)` lies in one of the regions `N1, N2, C4, C1, C2', N3', C3'` and
   `λ < 1` or `R < C_L`, a selected opaque outcome (`IsOpaqueOutcome`) exists.
2. **Every** selected opaque outcome `(qH, qL, P)` satisfies, region by region:
   * on `N1`, `C1`, `C4`: `qH = qL = 0` (case 1) and
     `Π_O = Π_O1 = λθα − (λθ + (1 − λ)(1 − θ))R`;
   * on `N2`: `qH = 1, qL = 0` (case 2) and `Π_O = Π_O2 = θ(α + β) − θR`;
   * on `N3'`: `qH = qL = 1` (case 3) and
     `Π_O = Π_O3 = λθ(α + β) + (1 − λ)(1 − θ)β − (λθ + (1 − λ)(1 − θ))R`;
   * on `C3'`: `qH = 1`, `qL = p_L = (αθ(1 − λ) − (R − β)θ(1 − λ))/((1 − θ)λ(R − β))` (case 5,
     eq. (A.4)) and `Π_O = Π_O5 = ((2λ − 1)/λ) θ(α + β − R)`;
   * on `C2'`: both types mix, `0 < qH < 1` and `0 < qL < 1` (case 9), and
     `Π_O = Π_O9 = (R − β)(2λ − 1)(α + β − R)(λθ(α − R) − (1 − θ)(1 − λ)R) / (R(2λ − 1)(α + β − R) − αβλ²)`.

**Formalization Note.** The printed Lemma 1 assigns case 4 (payoff `Π_O4`) to a triangle of the
printed region C2 and excludes case 9; App. A.1's case-4 range (p.43) reverses the inequality its
own condition gives, case 4 is never the selected outcome, and on `C2'` the selected outcome is
the both-types-mixing case 9. `Π_O4` is therefore not stated. At `λ = 1` the opaque game has no
equilibrium on `C2'`, so clause 1 excludes that case and the `C2'` part of clause 2 is vacuous
there. -/
theorem lemma_1 (p : Params) (hp : Standing p) (CH CL : ℝ) (hCH : 0 < CH) (hHL : CH < CL) :
    ((∃ r : Region, InRegion p CH CL r) → (p.lam < 1 ∨ p.R < CL) →
      ∃ (qH qL : ℝ) (P : OState → ℝ), IsOpaqueOutcome p CH CL qH qL P) ∧
    ∀ (qH qL : ℝ) (P : OState → ℝ), IsOpaqueOutcome p CH CL qH qL P →
      ((InRegion p CH CL .N1 ∨ InRegion p CH CL .C1 ∨ InRegion p CH CL .C4) →
        qH = 0 ∧ qL = 0 ∧
        firmPayoffO p qH qL P =
          p.lam * p.θ * p.α - (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R) ∧
      (InRegion p CH CL .N2 →
        qH = 1 ∧ qL = 0 ∧ firmPayoffO p qH qL P = p.θ * (p.α + p.β) - p.θ * p.R) ∧
      (InRegion p CH CL .N3' →
        qH = 1 ∧ qL = 1 ∧
        firmPayoffO p qH qL P =
          p.lam * p.θ * (p.α + p.β) + (1 - p.lam) * (1 - p.θ) * p.β -
            (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R) ∧
      (InRegion p CH CL .C3' →
        qH = 1 ∧
        qL = (p.α * p.θ * (1 - p.lam) - (p.R - p.β) * p.θ * (1 - p.lam)) /
          ((1 - p.θ) * p.lam * (p.R - p.β)) ∧
        firmPayoffO p qH qL P = (2 * p.lam - 1) / p.lam * p.θ * (p.α + p.β - p.R)) ∧
      (InRegion p CH CL .C2' →
        0 < qH ∧ qH < 1 ∧ 0 < qL ∧ qL < 1 ∧
        firmPayoffO p qH qL P =
          (p.R - p.β) * (2 * p.lam - 1) * (p.α + p.β - p.R) *
              (p.lam * p.θ * (p.α - p.R) - (1 - p.θ) * (1 - p.lam) * p.R) /
            (p.R * (2 * p.lam - 1) * (p.α + p.β - p.R) - p.α * p.β * p.lam ^ 2)) := by sorry

end AlgoTransparency
