-- Prove2me | Theorems.Thm_EllsbergLearning_drift_comparison
-- name    : EllsbergLearning.drift_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:52.735605+00:00
-- url     : https://prove2.me/theorems/2cb3c1a6-1d76-4e13-a1af-a4347acc3bb8
-- title:
--   §5.1, p.27 — $(\tilde f-f)\,v_z\ge0$ (corrected: prior odds $m/(1-m)$, case $Z_t\ge\tilde z_t$; $u_2^{**}$)
-- statement:
--   Assume the standing assumptions, payoff symmetry and the indifference point $(\underline\pi,\overline\pi,\tilde z)$. For every $t$, every $z$ and every prior $m\in[\underline m_0,\overline m_0]$,
--   $$\big(\hat\theta^{\mu^m}_t(z)-f(t,z)\big)\,\partial_zv(t,z)\ge0,$$
--   where $\hat\theta^{\mu^m}_t(z)$ is the drift of $Z$ under the prior $\mu^m$ and $f$ is the worst-case drift (46), both
--
--   1. for $v$ of (44), when $(r^R,r^l)$ solves (32) and $u_2<u_2^{**}$, and
--   2. for $v$ of (50), when $(r^l_1,r^l_2)$, $(r^R_1,r^R_2)$ solve (31), (30) and $r^l_1\le\overline\pi$.
--
--   Every other prior pushes the value process up relative to $P^*$; this is why $P^*$ is the worst case.
--
--   Differences from the source:
--   - correction: $\tilde f(t,Z_t,\eta_t)=\theta_1-\frac{\theta_1-\theta_0}{1+\frac{\eta_t}{1-\eta_t}\varphi}$ and "Argue similarly for $Z_t<\tilde z_t$" → the drift $\hat\theta^{\mu^m}_t(z)$ under the prior $m\in[\underline m_0,\overline m_0]$ (odds $m/(1-m)$), and the second case $z\ge\tilde z_t$; reason: $\eta_t$ is a density generator (a drift divided by $-\sigma$), not a probability; the page's own justification uses the prior $m$, and repeating the case $Z_t<\tilde z_t$ is a typo
--   - generalization: case (a.ii): $r_1^l>\overline\pi$ → $u_2<u_2^{**}$; reason: by (37) the two are equivalent whenever (31) has a solution; $u_2<u_2^{**}$ also covers the case where (31) has none, and the paper's proof of (a.ii) uses only $u_2<u_2^{**}$
--   - correction: (34): $u_2^{**}=\tfrac{\hat c}{2}[\cdots]+\tfrac{u_{00}-u_{01}}{2}$ → $u_2^{**}=\tfrac{\hat c}{2}[\cdots]+\tfrac{u_{00}+u_{01}}{2}$; reason: the printed value contradicts (37) and the paper's identity $u_2^{**}=g_1(\overline\pi;C_1,C_2)$ (p.26): in the Ellsberg instance $\alpha=1/8$, $c=0.01$, $\sigma=1$, $\epsilon=0.04$ (all assumptions hold) the printed $u_2^{**}\approx0.126<u_2=1/2$ while $r_1^l=\hat r\approx0.5244>\overline\pi=0.52$; the corrected value $\approx0.5011$ equals $g_1(\overline\pi)$ and $v_0$ of (26)
--   - encoding: posteriors $\underline m_t,\overline m_t$ by Bayesian updating (Liptser–Shiryaev, Theorem 9.1) → the closed form (12)–(13), as a function of $(t,z)$; reason: the paper's own formula; same objects
--   - generalization: a trajectory $(\tilde z_t)_{t\ge0}$ → a function $\tilde z:\mathbb R\to\mathbb R$ with the defining identities for every real $t$; reason: the closed forms extend to all real $t$; the paper's trajectory is the restriction to $t\ge0$, and uniqueness on $\mathbb R$ implies uniqueness on $[0,\infty)$
--   - generalization: times $t\ge 0$ → every real $t$ for the deterministic functions of $(t,z)$; reason: the closed forms (12)–(13) are defined for every real $t$; restricting to $t\ge0$ gives the paper's statement
--   - encoding: $f(t,z)$ of (46) → `drift`; reason: the paper uses the letter $f$ also for the boundary maps $\overline f,\underline f$ of p.21
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §5.1, p.27

import Definitions.Def_EllsbergLearning_ValueCandidates

open Set

namespace EllsbergLearning

/-- The drift comparison of §5.1, p.27 (Epstein & Ji, arXiv:1708.01890v2):
"(f̃(t, Z_t, η_t) − f(t, Z_t)) v_z(Z_t) ≥ 0". Under the standing assumptions of §3.1 and payoff
symmetry, with `(π̲, π̄, z̃)` the indifference point: for every `t`, every `z` and every prior
`m ∈ [m̲₀, m̄₀]`, the drift `θ̂^{µ^m}_t(z)` under the prior `µ^m` and the worst-case drift `f(t, z)`
of (46) satisfy `(θ̂^{µ^m}_t(z) − f(t, z)) · ∂_z v(t, z) ≥ 0`,

1. for `v` of (44) (case (a.ii): `(rᴿ, rˡ)` solves (32) and `u₂ < u₂**`), and
2. for `v` of (50) (case (a.i): `(r₁ˡ, r₂ˡ)`, `(r₁ᴿ, r₂ᴿ)` solve (31), (30), and `r₁ˡ ≤ π̄`).

**Formalization Note.** The page writes `f̃` with `η_t/(1 − η_t)` in place of the prior odds
`m/(1 − m)`, and "Argue similarly for `Z_t < z̃_t`" for the case `Z_t > z̃_t`; the statement uses the
drift of `Z` under the prior `µ^m`, as the parenthetical argument on p.27 does. `∂_z v` is
`deriv`; `v(t, ·)` is continuously differentiable (`lemma_5_1`, `lemma_5_1_case_a_i`). -/
theorem drift_comparison (p : Params) (hp : p.Valid) (hsym : p.PayoffSymmetry) (πL πU : ℝ)
    (zt : ℝ → ℝ) (hind : p.IsIndifference πL πU zt) :
    (∀ rR rl : ℝ, p.Solves32 πL πU rR rl → p.u₂ < p.u2StarStar πU rl →
      ∀ t z m : ℝ, m ∈ Icc p.mLo0 p.mUp0 →
        0 ≤ (p.thetaHat m t z - p.drift zt t z) * deriv (fun y => p.vA2 πL πU zt rR rl t y) z) ∧
    (∀ r1l r2l r1R r2R : ℝ, p.Solves31 r1l r2l → p.Solves30 r1R r2R → r1l ≤ πU →
      ∀ t z m : ℝ, m ∈ Icc p.mLo0 p.mUp0 →
        0 ≤ (p.thetaHat m t z - p.drift zt t z) * deriv (fun y => p.vA1 r1l r2l r1R r2R t y) z) := by sorry

end EllsbergLearning
