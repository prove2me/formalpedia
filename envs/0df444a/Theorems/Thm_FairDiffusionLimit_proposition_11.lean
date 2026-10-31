-- Prove2me | Theorems.Thm_FairDiffusionLimit_proposition_11
-- name    : FairDiffusionLimit.proposition_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:30.775339+00:00
-- url     : https://prove2.me/theorems/7cfd1f7d-885d-469d-9703-7ce0b0591268
-- title:
--   Proposition 11 — uniform $p$-th moment stability
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17). Assume the usual traffic condition (66) and the bounded workload condition (71). There are a time $t_0$ and an index $k_0$ such that for all $t\ge t_0$
--   $$\lim_{|x|\to\infty}\ \sup_{k\ge k_0}\ E\frac1{|x|^p}\Big|\hat W^k(|x|t;x)\Big|^p=0,\tag{74}$$
--   where $\hat W^k(\cdot;x)$ is the workload of network $k$ started from $\hat\Xi^k(0)=x$.
--
--   This is the uniform moment stability from which the return-time bound of Proposition 12 follows.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). The limit is stated in $\varepsilon$–$M$ form over all realizations.
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - encoding: (71) with sup_{0≤s≤t}|Ŵ^k(s)| and sup_{0≤s≤t}|X̂^k(s)|, "any sample-path" → for every k ≥ 1, every path satisfying the dynamics whose counts (4) are finite (all nonnegative primitive sequences with unbounded partial sums, all initial states), every t ≥ 0 and every bound M of |X̂^k| on [0, t]: |Ŵ^k(s)| ≤ κ(|Ŵ^k(0)| + M) on [0, t]; reason: equivalent to the supremum form, also when a supremum is infinite; "any sample-path" read literally; a primitive sequence with bounded partial sums makes the maxima in (4) infinite and is not a sample path of the model
--   - encoding: expectations E|·|^q → lower Lebesgue integrals ∫⁻ ENNReal.ofReal(|·|^q) in [0, ∞]; reason: the same value, with no junk value for non-integrable variables
--   - encoding: lim_{|x|→∞} sup_{k≥k₀} E|Ŵ^k(|x|t;x)|^p/|x|^p = 0 → ∀ ε > 0 ∃ M₀ ∀ x with |x| ≥ M₀ ∀ k ≥ k₀ ∀ realization from Ξ̂^k(0) = x: E … ≤ ε; reason: the ε–M form of the limit of a nonnegative quantity
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Proposition 11, p.23 (PDF 23)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Proposition 11** (uniform `p`-th moment stability; Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 23): under (66) and (71) there
are a time `t₀` and an index `k₀` such that for all `t ≥ t₀`
`lim_{|x|→∞} sup_{k≥k₀} E|Ŵ^k(|x|t; x)|^p/|x|^p = 0` (74).

**Formalization Note.** The limit is written in `ε`–`M` form; `Ŵ^k(·; x)` is the process of any
realization of network `k` from `δ_{kx}` (so `Ξ̂^k(0) = x`). -/
theorem proposition_11 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hAθ : S.UsualTraffic) (hBW : S.BoundedWorkload) :
    ∃ t0 : ℝ, ∃ k0 : ℕ, ∀ t : ℝ, t0 ≤ t → ∀ ε : ℝ, 0 < ε → ∃ M0 : ℝ, ∀ x : State R,
      M0 ≤ stNorm x → ∀ k, k0 ≤ k → ∀ Rz : NetSeq.Realization S k (Measure.dirac ((k : ℝ) • x)),
        ∫⁻ ω, ENNReal.ofReal (l1 ((stNorm x)⁻¹ • S.hatW k (Rz.pd ω) (stNorm x * t)) ^ S.p) ∂(Rz.C.P)
          ≤ ENNReal.ofReal ε := by sorry

end FairDiffusionLimit
