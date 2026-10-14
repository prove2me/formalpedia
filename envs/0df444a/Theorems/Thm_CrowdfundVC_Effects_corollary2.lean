-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_corollary2
-- name    : CrowdfundVC.Effects.corollary2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:45.005646+00:00
-- url     : https://prove2.me/theorems/af1bc632-51ee-4791-8f42-9cce3de8f4fc
-- title:
--   Corollary 2, PDF p. 21 — if e1 ≥ R0, crowdfunding raises the equity share when Δa ≤ 0 and reduces it when Δa > 0
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta \le 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), suppose $e_1 \ge R_0$, so that without crowdfunding the startup offers $\alpha^o = R_0/e_1$ (Proposition 1). Then the share $\alpha^c$ of Proposition 4 satisfies
--   $$\Delta_a \le 0 \implies \alpha^c \ge \frac{R_0}{e_1}, \qquad \Delta_a > 0 \implies \alpha^c < \frac{R_0}{e_1} \ \text{ (when } \rho > 0,\ p_1 < 1).$$
--
--   Crowdfunding thus strengthens the investing VC's equity position when the startup induces pre-crowdfunding investment and weakens it when the startup induces a delay. (The corollary's last sentence, no VC investment without crowdfunding when $e_1 < R_0$, is part (1) of Proposition 1.)
--
--   **Formalization Note** "Raises" is weak: at $p_2 = p_1$ one has $\alpha_0 = R_0/e_1$ and the two shares coincide. "Reduces" is strict and carries the added hypotheses $\rho > 0$ and $p_1 < 1$, which give $\tilde e_1|S > e_1$ (at $\rho = 0$ the two shares coincide); the "raises" half is stated without them. $0 \le R_f$ is added as for every item.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 21, Corollary 2; proof Online Appendix D, PDF p. 52 (OA p. 25)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Corollary 2 (p. 21). If `e1 ≥ R0`, crowdfunding (weakly) raises the equity share offered to the
investing VC (`αᶜ ≥ R0/e1`) when `Δa ≤ 0`, and strictly reduces it (`αᶜ < R0/e1`) when `Δa > 0`, `ρ > 0` and `p1 < 1`. -/
theorem corollary2 (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β ≤ 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    P.R0 ≤ e1 P →
      (deltaA P ≤ 0 → P.R0 / e1 P ≤ alphaC P) ∧
      (0 < P.ρ → P.p1 < 1 → 0 < deltaA P → alphaC P < P.R0 / e1 P) := by sorry

end CrowdfundVC.Effects
