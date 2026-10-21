-- Prove2me | Theorems.Thm_CyberShare_Sharing_lemma_c1
-- name    : CyberShare.Sharing.lemma_c1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:33.109798+00:00
-- url     : https://prove2.me/theorems/3c2af1f5-2363-43fc-ba17-bfda25b5c818
-- title:
--   Lemma C.1 — unique interior investment equilibrium above (C.12)
-- statement:
--   Under the standing assumptions there is a positive investment-cost threshold $\bar\kappa$ such that, for every $\kappa>\bar\kappa$ and every $b\in[0,1]$, the printed bound $\underline\delta(\kappa)$ of equation (C.12) lies strictly between $0$ and $a-c$. For each attack impact $\delta\in(\underline\delta(\kappa),a-c)$ and every sharing profile, the investment subgame has exactly one equilibrium. Every investment prescribed at this equilibrium is interior:
--
--   $$
--   0<K_i(y_i,y_j)<\frac{\delta}{\gamma},\qquad i=1,2.
--   $$
--
--   This result supplies the subgame outcomes used to compare sharing decisions in Proposition 2.
--
--   **Formalization Note** The bound is the paper's printed (C.12), treated as sufficient for interiority. The printed claim that it is the unique threshold is stronger than the displayed formula supports; the mission does not claim necessity. Uniqueness ranges over all investment equilibria, including any boundary candidate, while the unique equilibrium is interior.
-- source:
--   August, Noh, Shamir & Shin, Cyberattacks, Operational Disruption and Investment in Resilience Measures, SSRN 4032257 (version of 2022-02-10), p. A.3 (PDF 35), Lemma C.1; p. A.8 (PDF 40), (C.12); https://ssrn.com/abstract=4032257

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

namespace CyberShare.Sharing

/-- Lemma C.1, p. A.3 (PDF 35), with the printed sufficient bound (C.12), p. A.8 (PDF 40). -/
theorem lemma_c1 (a c gamma thL thH rho lam : ℝ)
    (h : BaseStanding a c gamma thL thH rho lam) :
    ∃ kappaBar : ℝ, 0 < kappaBar ∧ ∀ kappa : ℝ, kappaBar < kappa →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        ∀ delta : ℝ, deltaLow P0 < delta → delta < a - c →
          let P : Params := { P0 with delta := delta }
          ∀ s1 s2 : Dec,
            ∃ pair : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
              IsInvEq P s1 s2 pair.1 pair.2 ∧
              (∀ y y' : Sig, 0 < pair.1 y y' ∧ pair.1 y y' < delta / gamma ∧
                0 < pair.2 y y' ∧ pair.2 y y' < delta / gamma) ∧
              ∀ pair' : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
                IsInvEq P s1 s2 pair'.1 pair'.2 → pair' = pair := by sorry

end CyberShare.Sharing
