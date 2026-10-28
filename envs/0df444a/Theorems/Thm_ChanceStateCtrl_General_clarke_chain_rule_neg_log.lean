-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_clarke_chain_rule_neg_log
-- name    : ChanceStateCtrl.General.clarke_chain_rule_neg_log
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:39.257043+00:00
-- url     : https://prove2.me/theorems/c41ef903-fbcb-4226-a0da-2ad9bb485d9d
-- title:
--   Proof of Proposition 2.6, p. 8 (citing [10, Thm 2.3.9(ii)]) — ∂^C(−log φ + log p)(u*) = −(1/φ(u*)) ∂^C φ(u*)
-- statement:
--   Let $U$ be a real normed space, $\varphi:U\to\mathbb R$ locally Lipschitzian around $u^*$ with $\varphi(u^*)>0$, and $p>0$. Then the Clarke subdifferential of $\tilde\varphi=-\log\varphi+\log p$ at $u^*$ is
--   $$
--   \partial^C\tilde\varphi(u^*)=-\frac{1}{\varphi(u^*)}\,\partial^C\varphi(u^*).
--   $$
--
--   This chain rule converts the multiplier rule for the convex reformulation (20) back into one for the probability function $\varphi$ itself, which is how condition (21) arises.
--
--   **Formalization Note** The paper states this citing [10, Theorem 2.3.9 (ii)]. The logarithm is the real logarithm: $\varphi$ is positive on a neighbourhood of $u^*$ and the Clarke subdifferential only depends on values near $u^*$, so this is the same function as the extended-valued $\tilde\varphi$ there. The right-hand side is the pointwise scalar multiple of the set $\partial^C\varphi(u^*)$.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 8, proof of Proposition 2.6, display after the citation of [10, Proposition 2.2.7]; stated in this paper, citing [10, Theorem 2.3.9 (ii)]

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem clarke_chain_rule_neg_log {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (φ : U → ℝ) (us : U) (hφ_lip : LocLipAt φ us) (hφ_pos : 0 < φ us) (p : ℝ) (hp : 0 < p) :
    clarkeSubdiff (fun u => -Real.log (φ u) + Real.log p) us =
      (-(φ us)⁻¹) • clarkeSubdiff φ us := by sorry

end ChanceStateCtrl.General
