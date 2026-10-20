-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_lhs15_log_concave_bell
-- name    : CryptoMembership.PerfectInfo.lhs15_log_concave_bell
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:49.164897+00:00
-- url     : https://prove2.me/theorems/40b40bd3-8124-4404-8286-3840a5980b15
-- title:
--   A.2, pp. 33–34 (PDF 34–35) — the LHS of (15) is positive, strictly log-concave in s, and tends to 0 as s → ±∞
-- statement:
--   Under the standing assumptions, let
--   $$L(s)=e^{(1-\eta_c+\sqrt{\tau_\varepsilon/\tau_e})s}\,\Phi\big(\eta_c\tau_\varepsilon^{-1/2}-s\,\tau_\varepsilon^{1/2}\big)$$
--   be the left-hand side of (15). Then
--
--   1. $L(s)>0$ for every $s$;
--   2. $s\mapsto\log L(s)$ is strictly concave on $\mathbb R$;
--   3. $L(s)\to0$ as $s\to-\infty$ and as $s\to+\infty$.
--
--   So $L$ is a log-concave bell curve in $s$, which is what makes the equilibrium count at most two.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), A.2, pp. 33–34 (PDF 34–35)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

open Filter Topology

theorem lhs15_log_concave_bell (P : Params) (hP : P.Standing) :
    (∀ s : ℝ, 0 < lhs15 P s) ∧
    StrictConcaveOn ℝ Set.univ (fun s => Real.log (lhs15 P s)) ∧
    Tendsto (lhs15 P) atBot (𝓝 0) ∧
    Tendsto (lhs15 P) atTop (𝓝 0) := by sorry

end CryptoMembership.PerfectInfo
