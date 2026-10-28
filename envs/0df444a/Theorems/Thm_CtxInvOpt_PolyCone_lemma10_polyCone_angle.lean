-- Prove2me | Theorems.Thm_CtxInvOpt_PolyCone_lemma10_polyCone_angle
-- name    : CtxInvOpt.PolyCone.lemma10_polyCone_angle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:13.041546+00:00
-- url     : https://prove2.me/theorems/74099726-befb-45eb-a5f4-53df0fec8bc4
-- title:
--   Lemma 10, p. 25 — the polyhedral cone of η-separated effective differences has α(K) ≤ arccos(η^{d−1}/d^{3/2})
-- statement:
--   Let $d\ge2$, $0<\eta\le1$ and $0\le p\le d$. Let $\delta_1,\dots,\delta_p\in\mathbb R^d$ be unit vectors, each at distance at least $\eta$ from the span of the earlier ones:
--   $$\|\delta_i-\Pi_{\delta_1,\dots,\delta_{i-1}}(\delta_i)\|\ \ge\ \eta,\qquad i=2,\dots,p,$$
--   where $\Pi$ denotes orthogonal projection onto the span. Let $\Delta=\operatorname{span}\{\delta_1,\dots,\delta_p\}$ and
--   $$K=\{c\in\Delta:\ c'\delta_i\ge0,\ i=1,\dots,p\} \tag{14}$$
--   the polyhedral cone they cut out inside $\Delta$. Then its uncertainty angle satisfies
--   $$\alpha(K)\ \le\ \arccos\!\Big(\frac{\eta^{d-1}}{d^{3/2}}\Big).$$
--
--   In the paper the $\delta_i$ are the unit effective differences that triggered the subspace updates up to period $t$, and $K=K_t$ contains the projected knowledge set. The bound says that after every subspace update the knowledge set is pointed within the new subspace, with an aperture controlled by $\eta$ and $d$ alone; the algorithm restarts its ellipsoidal cone from the revolution cone of this aperture.
--
--   **Formalization Note** "For every period $t$" becomes "for every family $\delta$ obeying the subspace updating rule". The rule's strict "$\|r^\pi_i\|>\eta$" is relaxed to "$\ge\eta$", Lemma B-4's form, which gives a stronger statement; the first vector carries no condition (its residual is $\|\delta_1\|=1$). The case $p=0$ is the first period, $\tau$ empty, $K=\{0\}$. Only the angle bound of Lemma 10 is posed: the inclusion $\Pi_{\Delta_t}(C(\mathcal I_t))\subseteq K_t$ concerns the algorithm's run and the polynomial-time computation of the circumcenter is a complexity claim. The cone is intersected with $\Delta$: without it the bound is false for $p<d$. $d\ge2$ is the paper's standing assumption (§2); $d^{3/2}$ is the real power.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 25, Lemma 10 (angle bound), (14); p. 24 (subspace updating rule); proof App-19–App-20

import Mathlib
import Definitions.Def_CtxInvOpt_PolyCone_Cones

namespace CtxInvOpt.PolyCone

/-- **Lemma 10 (Uncertainty angle of polyhedral cone), angle bound, arXiv:2106.14015v3, p. 25.**
Let `0 < η ≤ 1`, `d ≥ 2`, `p ≤ d`, and let `δ_0, …, δ_{p-1}` be unit vectors of `ℝ^d` such that each `δ_i`
with `i ≥ 1` is at distance at least `η` from `span{δ_0, …, δ_{i-1}}` (the subspace updating rule of
§5). Then the polyhedral cone `K = {c ∈ span{δ_i} : c′δ_i ≥ 0 ∀ i}` of (14) has uncertainty angle
`α(K) ≤ arccos(η^{d−1}/d^{3/2})`. For `p = 0` (the first period, `τ` empty) `K = {0}`. -/
theorem lemma10_polyCone_angle {d p : ℕ} (hd : 2 ≤ d) (hpd : p ≤ d) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (δ : Fin p → EuclideanSpace ℝ (Fin d)) (hunit : ∀ i, ‖δ i‖ = 1)
    (hsep : ∀ i : Fin p, 0 < i.val →
      η ≤ ‖δ i - (Submodule.span ℝ (δ '' {j | j < i})).starProjection (δ i)‖) :
    CtxInvOpt.Offline.uncAngle (polyCone δ) ≤ Real.arccos (η ^ (d - 1) / (d : ℝ) ^ ((3 : ℝ) / 2)) := by sorry

end CtxInvOpt.PolyCone
