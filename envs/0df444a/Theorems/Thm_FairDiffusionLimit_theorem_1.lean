-- Prove2me | Theorems.Thm_FairDiffusionLimit_theorem_1
-- name    : FairDiffusionLimit.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:36.303987+00:00
-- url     : https://prove2.me/theorems/b8c72be7-070b-4f75-b82e-9ff4179e199e
-- title:
--   Theorem 1 — the diffusion limit [57]
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   Suppose the networks start so that the diffusion-scaled initial workloads converge to a (random) fixed-point state and the time-zero residuals vanish:
--   $$\hat W^k(0)\Rightarrow\hat W(0)\in\mathcal W,\tag{34}$$
--   $$|\hat U^k(0)|+|\hat V^k(0)|=\frac1k\big(|u^k(1)|+|v^k(1)|\big)\to0 .\tag{35}$$
--   Then, as $k\to\infty$,
--   $$\big(\hat W^k(t),\hat X^k(t),\hat Y^k(t),\hat Z^k(t)\big)\Rightarrow\big(\hat W(t),\hat X(t),\hat Y(t),\hat Z(t)\big),$$
--   where the limit solves the DCP (27)–(32): $\hat X$ is a Brownian motion with drift $\theta$ and covariance $\Upsilon$ of (33), independent of $\hat W(0)$, whose law is the limit in (34).
--
--   This is the heavy-traffic diffusion approximation of the PF network; the paper cites it from Ye–Yao (2012) [57].
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
--   - generalization: (35) …→ 0 a.s. → (35) in probability for each ε > 0; reason: the hypothesis is weakened (a.s. convergence on a common space implies convergence in probability), so the Lean theorem specializes to the printed one
--   - reading: the networks of Theorem 1 started from arbitrary initial states → any realization Rz k of network k from an initial law μ_k (independent of the primitives); reason: the Markov setting of p.10; (34) and (35) are statements about these laws
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Theorem 1, p.13 (PDF 13)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Theorem 1** (diffusion limit [57]; Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 13): under heavy traffic (11), if the
diffusion-scaled initial workloads converge, `Ŵ^k(0) ⇒ Ŵ(0) ∈ 𝒲` (34), and the time-zero residuals
vanish, `|Û^k(0)| + |V̂^k(0)| = (|u^k(1)| + |v^k(1)|)/k → 0` (35), then
`(Ŵ^k, X̂^k, Ŷ^k, Ẑ^k) ⇒ (Ŵ, X̂, Ŷ, Ẑ)`, the diffusion limit characterized by (27)–(32).

**Formalization Note.** `Rz k` is any realization of network `k`. (35) is assumed in probability (the
page's almost-sure convergence on a common space implies it). The limit's Brownian motion `X̂` is
independent of `Ŵ(0)`, whose law is the limit law of (34). `⇒` is `WeakConvUoc` (joint, u.o.c.). -/
theorem theorem_1 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (μ : ℕ → Measure (State R)) (Rz : ∀ k, NetSeq.Realization S k (μ k))
    (ν0 : ProbabilityMeasure (Fin R → ℝ)) (hν0 : (ν0 : Measure (Fin R → ℝ)) S.Wconeᶜ = 0)
    (h34 : Tendsto (fun k => lawPM (Rz k).C.P (fun ω => S.hatW k ((Rz k).pd ω) 0)
      ((Rz k).measurable_hatW 0)) atTop (𝓝 ν0))
    (h35 : ∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ => (Rz k).C.P
      {ω | ε < (l1 ((Rz k).X0 ω).2.1 + l1 ((Rz k).X0 ω).2.2) / k}) atTop (𝓝 0)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W X : Ω' → ℝ → Fin R → ℝ)
      (Y : Ω' → ℝ → Fin L → ℝ) (Z : Ω' → ℝ → Fin (R - L) → ℝ),
      S.IsDiffSol H P' W X Y Z ∧ P'.map (fun ω => W ω 0) = ν0 ∧
      WeakConvUoc (Ω := fun k => (Rz k).C.Ω) (fun k => (Rz k).C.P)
        (fun k ω t => (S.hatW k ((Rz k).pd ω) t, S.hatX k ((Rz k).pd ω) t, S.hatY k ((Rz k).pd ω) t,
          S.hatZ H k ((Rz k).pd ω) t))
        P' (fun ω t => (W ω t, X ω t, Y ω t, Z ω t)) := by sorry

end FairDiffusionLimit
