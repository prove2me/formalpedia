-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_eq_45
-- name    : CachonCoord.InternalMarket.eq_45
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:09:53.431862+00:00
-- url     : https://prove2.me/theorems/fbc75c86-547b-4115-8c18-715766e2a6f5
-- title:
--   Eq. (45), p. 93 — Π(e) = K e^{(η−1)/η} − c(e) is strictly concave and e° > 0 is optimal iff ((η−1)/η)(e°)^{−1/η}K − c′(e°) = 0
-- statement:
--   In the model of §6.9.1, let $K=E\big[(A_1^\eta+A_2^\eta)^{1/\eta}Y^{(\eta-1)/\eta}\big]$, the integrand being integrable. The total expected supply chain profit $\Pi(e)=E[\pi(A,Ye)]-c(e)$ satisfies:
--
--   1. $\Pi(e)=K\,e^{(\eta-1)/\eta}-c(e)$ for every $e\ge0$;
--   2. $\Pi$ is strictly concave on $[0,\infty)$;
--   3. for every $e>0$,
--   $$
--   \Pi'(e)=\Big(\frac{\eta-1}{\eta}\Big)e^{-1/\eta}K-c'(e);
--   $$
--   4. an effort $e^o>0$ maximizes $\Pi$ over $[0,\infty)$ if and only if
--   $$
--   \Big(\frac{\eta-1}{\eta}\Big)(e^o)^{-1/\eta}\,E\big[(A_1^\eta+A_2^\eta)^{1/\eta}Y^{(\eta-1)/\eta}\big]-c'(e^o)=0. \qquad (45)
--   $$
--
--   Equation (45) characterizes the supply chain optimal effort $e^o$, the target of the manager's compensation scheme (46).
--
--   **Formalization Note** The page asserts that a unique optimum exists and satisfies (45); its existence is not formalized here (it depends on $c$), so the statement is the characterization "optimal iff (45)" for interior efforts, and uniqueness follows from strict concavity (item 2). The page prints $\Pi'(e^0)$ with a zero for the superscript $o$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, Eq. (45), p. 93

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- Eq. (45), §6.9.1, p. 93 (Cachon 2003, 3rd draft). Let
`K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` (assumed integrable). Then, on `e ≥ 0`:
1. total expected supply chain profit is `Π(e) = E[π(A, Ye)] − c(e) = K e^{(η−1)/η} − c(e)`;
2. `Π` is strictly concave on `[0, ∞)`;
3. for `e > 0`, `Π'(e) = ((η − 1)/η) e^{−1/η} K − c'(e)`;
4. an effort `e° > 0` maximizes `Π` over `[0, ∞)` if and only if
   `((η − 1)/η) (e°)^{−1/η} K − c'(e°) = 0`. -/
theorem eq_45 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hint : Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
      M.Y ω ^ ((M.η - 1) / M.η)) M.P) :
    (∀ e : ℝ, 0 ≤ e → M.chainProfit e = M.K * e ^ ((M.η - 1) / M.η) - M.c e) ∧
    StrictConcaveOn ℝ (Set.Ici 0) M.chainProfit ∧
    (∀ e : ℝ, 0 < e →
      HasDerivAt M.chainProfit ((M.η - 1) / M.η * e ^ (-1 / M.η) * M.K - M.c' e) e) ∧
    ∀ eo : ℝ, 0 < eo →
      (IsMaxOn M.chainProfit (Set.Ici 0) eo ↔
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0) := by sorry

end CachonCoord.InternalMarket
