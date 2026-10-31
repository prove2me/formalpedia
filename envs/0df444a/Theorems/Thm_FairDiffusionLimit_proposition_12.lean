-- Prove2me | Theorems.Thm_FairDiffusionLimit_proposition_12
-- name    : FairDiffusionLimit.proposition_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:29.596328+00:00
-- url     : https://prove2.me/theorems/1ea278a5-4555-4843-958f-ea8e37dee850
-- title:
--   Proposition 12 — the return-time bound (77) (corrected: supremum over $k\ge k_0$)
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17). Assume the usual traffic condition (66) and the bounded workload condition (71). There are constants $\kappa,\delta>0$, a compact set $C\subset\mathcal X$ and an index $k_0$ such that for every initial state $x\in\mathcal X$
--   $$\sup_{k\ge k_0}E\int_0^{\tau^k_C(\delta)}\big(1+|\hat\Xi^k(t;x)|^{p-1}\big)\,dt\le\kappa(1+|x|^p),\tag{77}$$
--   where $\tau^k_C(\delta)=\inf\{t\ge\delta:\hat\Xi^k(t)\in C\}$ is the return time to $C$ after time $\delta$.
--
--   This drift-type bound gives the tightness and uniform moment bound of Proposition 13.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). The time integral is a lower Lebesgue integral over $[0,\tau)$ in $[0,\infty]$.
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
--   - correction: sup_k over all networks k → ∃ k₀, sup over k ≥ k₀; reason: as printed (77) is false: L = R = 1, A = c = β = 1, Poisson arrivals and exponential work, ν^k = 1, λ¹ = 2, λ^k = 1 − 1/k (k ≥ 2) satisfy every standing assumption, (66) and (71) (κ = 2); network 1 is transient, so for every compact C the return time τ¹_C(δ) is infinite with positive probability from large x and the left side is +∞; the proof (D.2) uses Proposition 11’s k ≥ k₀
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Proposition 12, p.24 (PDF 24)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Proposition 12** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 24), corrected: under (66) and (71) there are constants
`κ, δ > 0`, a compact set `C ⊂ 𝒳` and an index `k₀` such that for every initial state `x ∈ 𝒳`,
`sup_{k≥k₀} E ∫₀^{τ^k_C(δ)} (1 + |Ξ̂^k(t; x)|^{p−1}) dt ≤ κ(1 + |x|^p)` (77), where
`τ^k_C(δ) = inf{t ≥ δ : Ξ̂^k(t) ∈ C}`.

**Formalization Note.** The page takes `sup_k` over all `k`; a network with small `k` can be
overloaded (the limits (10) constrain only large `k`), making the left side infinite, so the supremum
is over `k ≥ k₀`, which is what the proof (via Proposition 11) gives. The time integral is a lower
Lebesgue integral over `[0, τ)` in `[0, ∞]` (`τ = ∞` allowed). -/
theorem proposition_12 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hAθ : S.UsualTraffic) (hBW : S.BoundedWorkload) :
    ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧ ∃ C : Set (State R), IsCompact C ∧ C ⊆ {x | 0 ≤ x} ∧
      ∃ k0 : ℕ, ∀ x : State R, ∀ k, k0 ≤ k → ∀ Rz : NetSeq.Realization S k (Measure.dirac ((k : ℝ) • x)),
        ∫⁻ ω, (∫⁻ t in {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < S.returnTime k C δ (Rz.pd ω)},
            ENNReal.ofReal (1 + stNorm (S.hatXi k (Rz.pd ω) t) ^ (S.p - 1))) ∂(Rz.C.P)
          ≤ ENNReal.ofReal (κ * (1 + stNorm x ^ S.p)) := by sorry

end FairDiffusionLimit
