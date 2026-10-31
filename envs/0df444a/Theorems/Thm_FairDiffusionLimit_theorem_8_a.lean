-- Prove2me | Theorems.Thm_FairDiffusionLimit_theorem_8_a
-- name    : FairDiffusionLimit.theorem_8_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:05.033727+00:00
-- url     : https://prove2.me/theorems/92bddb3a-7442-4804-9585-d68f40825032
-- title:
--   Theorem 8(a) — the usual traffic condition $A\theta<0$ is necessary and sufficient for stability of the deterministic DCP
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   The deterministic DCP (38)–(43) is
--   $$\hat w(t)=\hat w(0)+\theta t+BG\hat y(t)+BH\hat z(t)\ge0,\quad G^T\hat w(t)\ge0,\quad \hat y\ \text{nondecreasing},\ \hat y(0)=0,\quad \int_0^\infty\hat w^TG\,d\hat y=0,\quad H^T\hat w=0,\quad \hat z(0)=0,$$
--   and it is **stable** if there is a time $T$ such that every solution with $|\hat w(0)|\le1$ has $\hat w(t)=0$ for all $t\ge T$. Then
--   $$A\theta<0\ \text{(componentwise)}\iff\text{the deterministic DCP (38)–(43) is stable.}$$
--
--   This identifies the usual traffic condition as the exact condition for stability of the fluid-type limit of the networks; it feeds Theorems 4 and 7.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). Solutions of the DCP are continuous paths.
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: DCP (27)–(32) / (38)–(43) with ∫ wᵀG dy = 0 → continuous paths on [0, ∞); (30)/(41) as "y_ℓ is constant on every [s, t] on which (Gᵀw)_ℓ > 0"; reason: the DCP is posed for continuous processes (p.12–13); for continuous w with Gᵀw ≥ 0 and nondecreasing y the two forms of (30) are equivalent
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Theorem 8(a), p.19 (PDF 19)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Theorem 8(a)** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 19): the usual traffic condition `Aθ < 0` (66) is necessary
and sufficient for the deterministic DCP (38)–(43) to be stable. -/
theorem theorem_8_a {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H) :
    S.UsualTraffic ↔ S.DetStable H := by sorry

end FairDiffusionLimit
