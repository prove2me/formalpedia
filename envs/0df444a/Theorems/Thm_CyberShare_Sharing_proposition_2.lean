-- Prove2me | Theorems.Thm_CyberShare_Sharing_proposition_2
-- name    : CyberShare.Sharing.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:51.6432+00:00
-- url     : https://prove2.me/theorems/924cfd93-7f78-4a4a-80dd-1783ac6a3ee4
-- title:
--   Proposition 2, pinned technical form — sharing under weak competition and high impact
-- statement:
--   Fix demand intercept $a$, normal marginal cost $c$, resilience effectiveness $\gamma$, attack likelihoods $\theta_L<\theta_H$, high-state prior $\rho$, and signal accuracy $\lambda$ under the paper's standing assumptions. There is a positive $\bar\kappa$ such that every $\kappa>\bar\kappa$ admits two competition regions.
--
--   1. In Region L, there is $\underline b\in(0,1]$ such that for each $b\in(0,\underline b)$ there is a nonempty interval $(\delta_1,a-c)$ in which mutual sharing $(S,S)$ is the unique sharing equilibrium, and a nonempty interval $(\underline\delta(\kappa),\delta_2)$ in which mutual nonsharing $(N,N)$ is the unique sharing equilibrium. The second interval is intersected with the paper's standing range $\delta<a-c$.
--   2. In Region H, there is $\bar b\in[0,1)$ such that for $b\in(\bar b,1]$ and every admissible $\delta>\underline\delta(\kappa)$, mutual nonsharing $(N,N)$ is the unique sharing equilibrium.
--
--   The result identifies when voluntary cyberattack-signal sharing can arise in the paper's three-stage duopoly.
--
--   **Formalization Note** This is the pinned reading of the proof's technical statement on p. A.17. It requires $\delta_1<a-c$, $0<\underline\delta<a-c$, $\underline\delta<\delta_2$, $\underline b>0$, and $\bar b<1$ so none of the asserted regions can be empty by an endpoint choice. The existence of investment equilibria on path and after deviations is part of the sharing-equilibrium definition. The page's "is the equilibrium" is read as uniqueness in all three parts, matching the headline prediction that the firms share (do not share) in each region. The conditions $\theta_L<\theta_H$, $0<\rho<1$, and $c\ge0$ are disclosed additions.
-- source:
--   August, Noh, Shamir & Shin, Cyberattacks, Operational Disruption and Investment in Resilience Measures, SSRN 4032257 (version of 2022-02-10), p. 12 (PDF 13), Proposition 2; technical statement and proof pp. A.17–A.19 (PDF 49–51); https://ssrn.com/abstract=4032257

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

namespace CyberShare.Sharing

/-- Proposition 2, p. 12 (PDF 13), in the pinned technical reading of p. A.17 (PDF 49).
"Is the equilibrium" is read as the unique sharing equilibrium in all three parts. -/
theorem proposition_2 (a c gamma thL thH rho lam : ℝ)
    (h : BaseStanding a c gamma thL thH rho lam) :
    ∃ kappaBar : ℝ, 0 < kappaBar ∧ ∀ kappa : ℝ, kappaBar < kappa →
      (∃ bLow : ℝ, 0 < bLow ∧ bLow ≤ 1 ∧ ∀ b : ℝ, 0 < b → b < bLow →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        (∃ delta1 : ℝ, delta1 < a - c ∧
          ∀ delta : ℝ, delta1 < delta → 0 < delta → delta < a - c →
            IsSharingEq { P0 with delta := delta } .S .S ∧
            ∀ s1 s2 : Dec, IsSharingEq { P0 with delta := delta } s1 s2 →
              s1 = .S ∧ s2 = .S) ∧
        (∃ delta2 : ℝ, deltaLow P0 < delta2 ∧
          ∀ delta : ℝ, deltaLow P0 < delta → delta < delta2 → delta < a - c →
            IsSharingEq { P0 with delta := delta } .N .N ∧
            ∀ s1 s2 : Dec, IsSharingEq { P0 with delta := delta } s1 s2 →
              s1 = .N ∧ s2 = .N)) ∧
      (∃ bHigh : ℝ, 0 ≤ bHigh ∧ bHigh < 1 ∧ ∀ b : ℝ, bHigh < b → b ≤ 1 →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        ∀ delta : ℝ, deltaLow P0 < delta → delta < a - c →
          let P : Params := { P0 with delta := delta }
          IsSharingEq P .N .N ∧
          ∀ s1 s2 : Dec, IsSharingEq P s1 s2 → s1 = .N ∧ s2 = .N) := by sorry

end CyberShare.Sharing
