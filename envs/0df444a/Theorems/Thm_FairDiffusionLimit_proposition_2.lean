-- Prove2me | Theorems.Thm_FairDiffusionLimit_proposition_2
-- name    : FairDiffusionLimit.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:27.703888+00:00
-- url     : https://prove2.me/theorems/147549c0-66ce-4f76-a556-a13f6e6b4283
-- title:
--   Proposition 2 — diffusion limits from tight initial states after a time shift $t^k_0$
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   There is a constant $\kappa_w$, depending only on the network parameters, with the following property. Let the networks start from initial laws such that $\{\hat\Xi^k(0)\}$ is tight, and let $t^k_0\to0$ with $kt^k_0\to\infty$. Then every subsequence of $k$ has a further subsequence $\mathcal K$ along which
--   $$\Big(\hat W^k(t^k_0+t),\ \hat X^k(t^k_0+t)-\hat X^k(t^k_0),\ \hat Y^k(t^k_0+t)-\hat Y^k(t^k_0),\ \hat Z^k(t^k_0+t)-\hat Z^k(t^k_0)\Big)\Rightarrow\big(\hat W(t),\hat X(t),\hat Y(t),\hat Z(t)\big),$$
--   where the limit solves the DCP (27)–(32) with $\hat X$ a Brownian motion with drift $\theta$ and covariance $\Upsilon$, independent of $\hat W(0)$. Moreover
--   $$\hat W^k(t^k_0)\Rightarrow\hat W(0)\in\mathcal W\tag{36}$$
--   and, for every $M\ge0$,
--   $$\limsup_{k\to\infty,\,k\in\mathcal K}P\{\kappa_w|\hat\Xi^k(0)|\le M\}\le P\{|\hat W(0)|\le M\}.\tag{37}$$
--
--   This is the variation of Theorem 1 that applies to networks started in their stationary distributions, whose initial states need not lie in $\mathcal W$; it identifies the limit points in Theorem 14.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). "$\Rightarrow$" is joint weak convergence of processes, u.o.c. on $[0,\infty)$.
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: DCP (27)–(32) / (38)–(43) with ∫ wᵀG dy = 0 → continuous paths on [0, ∞); (30)/(41) as "y_ℓ is constant on every [s, t] on which (Gᵀw)_ℓ > 0"; reason: the DCP is posed for continuous processes (p.12–13); for continuous w with Gᵀw ≥ 0 and nondecreasing y the two forms of (30) are equivalent
--   - encoding: X̂ a Brownian motion with drift θ and covariance Υ (p.13) → published Reiman84.QueueLength.IsDriftedBM θ Υ: X̂(0) = 0, every path continuous, independent Gaussian increments; reason: X̂(0) = 0 is forced by (24); continuity of every path instead of almost every path changes no law
--   - reading: "where Ŵ(0) ∈ 𝒲 is the (given) initial state and X̂(t), the free process, is a Brownian motion" (p.13) → Ŵ(0) independent of X̂ (IsDiffSol); reason: the diffusion limit is driven by a Brownian motion independent of its initial state; the proof of Theorem 14 (p.25) uses this to identify the limit as the diffusion started from π̃₁
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - encoding: "⇒" weak convergence in D with u.o.c. convergence (pp.12–13) → WeakConvUoc: for every T ≥ 0 a coupling with the same laws on [0, T] and almost-sure uniform convergence on [0, T], jointly for all listed components; reason: the limits are continuous, so weak convergence in D[0, ∞) is equivalent to weak convergence of the restrictions to every [0, T] in the uniform topology (Skorohod representation)
--   - encoding: "for any subsequence of k, there exists a further subsequence 𝒦" → φ strictly increasing, ∃ ψ strictly increasing, 𝒦 = φ ∘ ψ; reason: the same subsequences
--   - encoding: "κ_w is a constant that depends only on network parameters" → ∃ κ_w placed after the network data and before every sequence, subsequence and initial law; reason: depending only on the network parameters is exactly this quantifier position
--   - reading: Ŵ(0) in (36) and (37) → the initial value of the same limit process; reason: the page uses the same Ŵ in all conclusions
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Proposition 2, p.14 (PDF 14)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Proposition 2** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 14): under heavy traffic (11) there is a constant `κ_w`
(depending only on the network parameters) with the following property. Let the initial states
`Ξ̂^k(0)` be tight and `t^k_0 → 0` with `k t^k_0 → ∞`. Then every subsequence of `k` has a further
subsequence `𝒦` along which
`(Ŵ^k(t^k_0+t), X̂^k(t^k_0+t) − X̂^k(t^k_0), Ŷ^k(t^k_0+t) − Ŷ^k(t^k_0), Ẑ^k(t^k_0+t) − Ẑ^k(t^k_0)) ⇒ (Ŵ, X̂, Ŷ, Ẑ)`,
the diffusion limit characterized by (27)–(32); moreover `Ŵ^k(t^k_0) ⇒ Ŵ(0) ∈ 𝒲` (36) and
`limsup_{k∈𝒦} P{κ_w|Ξ̂^k(0)| ≤ M} ≤ P{|Ŵ(0)| ≤ M}` for every `M ≥ 0` (37).

**Formalization Note.** `Rz k` is any realization of network `k` from an initial law `μ k`; tightness
is that of the laws `π̂ = μ_k ∘ (x ↦ x/k)⁻¹` of `Ξ̂^k(0)`. The limit's Brownian motion is independent
of `Ŵ(0)` (`IsDiffSol`). `⇒` is `WeakConvUoc` (joint, u.o.c.); (36) is weak convergence of laws. -/
theorem proposition_2 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H) :
    ∃ κw : ℝ, ∀ (μ : ℕ → Measure (State R)) (Rz : ∀ k, NetSeq.Realization S k (μ k)),
      IsTightMeasureSet (Set.range fun k => NetSeq.hatLaw k (μ k)) →
      ∀ t0 : ℕ → ℝ, Tendsto t0 atTop (𝓝 0) → Tendsto (fun k : ℕ => (k : ℝ) * t0 k) atTop atTop →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (W X : Ω' → ℝ → Fin R → ℝ) (Y : Ω' → ℝ → Fin L → ℝ) (Z : Ω' → ℝ → Fin (R - L) → ℝ)
          (hW : ∀ t, Measurable fun ω => W ω t),
          S.IsDiffSol H P' W X Y Z ∧
          WeakConvUoc (Ω := fun n => (Rz (φ (ψ n))).C.Ω) (fun n => (Rz (φ (ψ n))).C.P)
            (fun n ω t =>
              (S.hatW (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n)) + t),
               S.hatX (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n)) + t)
                 - S.hatX (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n))),
               S.hatY (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n)) + t)
                 - S.hatY (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n))),
               S.hatZ H (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n)) + t)
                 - S.hatZ H (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n)))))
            P' (fun ω t => (W ω t, X ω t, Y ω t, Z ω t)) ∧
          Tendsto (fun n => lawPM (Rz (φ (ψ n))).C.P
              (fun ω => S.hatW (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (t0 (φ (ψ n))))
              ((Rz (φ (ψ n))).measurable_hatW _))
            atTop (𝓝 (lawPM P' (fun ω => W ω 0) (hW 0))) ∧
          ∀ M : ℝ, 0 ≤ M →
            limsup (fun n => (Rz (φ (ψ n))).C.P
                {ω | κw * stNorm (((φ (ψ n) : ℕ) : ℝ)⁻¹ • (Rz (φ (ψ n))).X0 ω) ≤ M})
              atTop ≤ P' {ω | l1 (W ω 0) ≤ M} := by sorry

end FairDiffusionLimit
