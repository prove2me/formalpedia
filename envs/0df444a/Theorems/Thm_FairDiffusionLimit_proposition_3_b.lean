-- Prove2me | Theorems.Thm_FairDiffusionLimit_proposition_3_b
-- name    : FairDiffusionLimit.proposition_3_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:11.813141+00:00
-- url     : https://prove2.me/theorems/2863539a-dafa-4a29-aab3-0cbb041a0093
-- title:
--   Proposition 3(b) — mixed-scaling limits from tight initial states solve the deterministic DCP
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   There is a constant $\kappa_w$, depending only on the network parameters, with the following property. Let $m_k\to\infty$, let the networks start from initial laws such that $\{\hat\Xi^k(0)/m_k\}$ is tight, and let $t^k_0\to0$ with $kt^k_0\to\infty$. Then every subsequence of $k$ has a further subsequence $\mathcal K$ along which
--   $$\frac1{m_k}\Big(\hat X^k(m_k(t^k_0+t))-\hat X^k(m_kt^k_0)\Big)\Rightarrow\theta t,$$
--   $$\frac1{m_k}\Big(\hat W^k(m_k(t^k_0+t)),\ \hat Y^k(m_k(t^k_0+t))-\hat Y^k(m_kt^k_0),\ \hat Z^k(m_k(t^k_0+t))-\hat Z^k(m_kt^k_0)\Big)\Rightarrow(\hat w(t),\hat y(t),\hat z(t)),$$
--   where $(\hat w,\hat y,\hat z)$ is a random solution of the deterministic DCP (38)–(43). Moreover
--   $$\frac1{m_k}\hat W^k(m_kt^k_0)\Rightarrow\hat w(0)\in\mathcal W\tag{44}$$
--   and, for every $M\ge0$,
--   $$\limsup_{k\to\infty,\,k\in\mathcal K}P\{\kappa_w|\hat\Xi^k(0)/m_k|\le M\}\le P\{|\hat w(0)|\le M\}.\tag{45}$$
--
--   This mixed (fluid-of-diffusion) scaling limit is used in the proof of Lemma 10(b).
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). "$\Rightarrow$" is weak convergence of processes, u.o.c. on $[0,\infty)$, jointly for the listed components.
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - reading: "{(u_r(i), v_r(i)), i ≥ 2} are i.i.d." (p.8) → all u¹_r(i), v¹_r(i) (i ≥ 2) independent across i, r and between u and v, with laws F^a_r, F^s_r on [0, ∞); reason: the standard renewal network; the paper states no other dependence and interarrival times and work requirements are nonnegative
--   - encoding: (10) σ-convergence and the common primitives (12) → base laws F^a_r, F^s_r of u¹_r(2), v¹_r(2) with means 1/λ¹_r, ν¹_r; network k uses (λ¹_r/λ^k_r)u¹_r(i), (ν^k_r/ν¹_r)v¹_r(i); σ_{a,r}, σ_{s,r} are the resulting limits; reason: (12) determines every network’s primitives from network 1’s; the σ-limits then exist automatically
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: DCP (27)–(32) / (38)–(43) with ∫ wᵀG dy = 0 → continuous paths on [0, ∞); (30)/(41) as "y_ℓ is constant on every [s, t] on which (Gᵀw)_ℓ > 0"; reason: the DCP is posed for continuous processes (p.12–13); for continuous w with Gᵀw ≥ 0 and nondecreasing y the two forms of (30) are equivalent
--   - encoding: the network process Ξ(t) (pp.9–10) → Realization: a probability space with i.i.d. base primitives (PrimSpace), an initial state independent of them, a queue-length path solving (6)–(7) almost surely, and measurable Ξ(t), D(t), E(t), S(D(t)); reason: a probability space carrying the paper’s process; the measurability fields only state that these are random variables
--   - encoding: "⇒" weak convergence in D with u.o.c. convergence (pp.12–13) → WeakConvUoc: for every T ≥ 0 a coupling with the same laws on [0, T] and almost-sure uniform convergence on [0, T], jointly for all listed components; reason: the limits are continuous, so weak convergence in D[0, ∞) is equivalent to weak convergence of the restrictions to every [0, T] in the uniform topology (Skorohod representation)
--   - encoding: "for any subsequence of k, there exists a further subsequence 𝒦" → φ strictly increasing, ∃ ψ strictly increasing, 𝒦 = φ ∘ ψ; reason: the same subsequences
--   - encoding: "κ_w is a constant that depends only on network parameters" → ∃ κ_w placed after the network data and before every sequence, subsequence and initial law; reason: depending only on the network parameters is exactly this quantifier position
--   - encoding: "Ẑ^k(m_k(t^k_0 + t) − Ẑ^k(m_kt^k_0))" → Ẑ^k(m_k(t^k_0 + t)) − Ẑ^k(m_kt^k_0); reason: a misplaced parenthesis; the other components are increments
--   - reading: the limit (ŵ, ŷ, ẑ) "follows the specifications in (38-43)" and (44) "ŵ(0) ∈ 𝒲" → one random solution of (38)–(43) on a probability space, whose ŵ(0) is the limit in (44) and the right side of (45); reason: the page uses the same ŵ in all three conclusions
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Proposition 3(b), p.15 (PDF 15)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Proposition 3(b)** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 15), under heavy traffic (11): there is a constant `κ_w`
(depending only on the network parameters) with the following property. Let `m_k → ∞`, let the
initial states `Ξ̂^k(0)/m_k` be tight, and let `t^k_0 → 0` with `k t^k_0 → ∞`. Then every subsequence
of `k` has a further subsequence `𝒦` along which
`(X̂^k(m_k(t^k_0 + t)) − X̂^k(m_kt^k_0))/m_k ⇒ θt` and
`(Ŵ^k(m_k(t^k_0+t)), Ŷ^k(m_k(t^k_0+t)) − Ŷ^k(m_kt^k_0), Ẑ^k(m_k(t^k_0+t)) − Ẑ^k(m_kt^k_0))/m_k ⇒ (ŵ, ŷ, ẑ)`,
a (random) solution of the deterministic DCP (38)–(43); moreover `Ŵ^k(m_kt^k_0)/m_k ⇒ ŵ(0) ∈ 𝒲` (44)
and `limsup_{k ∈ 𝒦} P{κ_w|Ξ̂^k(0)/m_k| ≤ M} ≤ P{|ŵ(0)| ≤ M}` for every `M ≥ 0` (45).

**Formalization Note.** `Rz k` is any realization of network `k` from an initial law `μ k`;
`Ξ̂^k(0) = Ξ^k(0)/k`. `⇒` is `WeakConvUoc` (joint, u.o.c.); (44) is weak convergence of laws. The page's
`Ẑ^k(m_k(t^k_0 + t) − Ẑ^k(m_kt^k_0))` is read as `Ẑ^k(m_k(t^k_0 + t)) − Ẑ^k(m_kt^k_0)`. -/
theorem proposition_3_b {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H) :
    ∃ κw : ℝ, ∀ (μ : ℕ → Measure (State R)) (Rz : ∀ k, NetSeq.Realization S k (μ k)) (m : ℕ → ℝ),
      Tendsto m atTop atTop →
      IsTightMeasureSet (Set.range fun k =>
        (Rz k).C.P.map (fun ω => (m k)⁻¹ • ((k : ℝ)⁻¹ • (Rz k).X0 ω))) →
      ∀ t0 : ℕ → ℝ, Tendsto t0 atTop (𝓝 0) → Tendsto (fun k : ℕ => (k : ℝ) * t0 k) atTop atTop →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (w : Ω' → ℝ → Fin R → ℝ) (y : Ω' → ℝ → Fin L → ℝ) (z : Ω' → ℝ → Fin (R - L) → ℝ)
          (hw : ∀ t, Measurable fun ω => w ω t),
          (∀ᵐ ω ∂P', S.IsDCPSol H (fun t => t • S.θ) (w ω) (y ω) (z ω)) ∧
          WeakConvUoc (Ω := fun n => (Rz (φ (ψ n))).C.Ω) (fun n => (Rz (φ (ψ n))).C.P)
            (fun n ω t => (m (φ (ψ n)))⁻¹ •
              (S.hatX (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * (t0 (φ (ψ n)) + t))
                - S.hatX (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * t0 (φ (ψ n)))))
            P' (fun _ t => t • S.θ) ∧
          WeakConvUoc (Ω := fun n => (Rz (φ (ψ n))).C.Ω) (fun n => (Rz (φ (ψ n))).C.P)
            (fun n ω t => (m (φ (ψ n)))⁻¹ •
              (S.hatW (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * (t0 (φ (ψ n)) + t)),
               S.hatY (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * (t0 (φ (ψ n)) + t))
                 - S.hatY (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * t0 (φ (ψ n))),
               S.hatZ H (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * (t0 (φ (ψ n)) + t))
                 - S.hatZ H (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * t0 (φ (ψ n)))))
            P' (fun ω t => (w ω t, y ω t, z ω t)) ∧
          Tendsto (fun n => lawPM (Rz (φ (ψ n))).C.P
              (fun ω => (m (φ (ψ n)))⁻¹ •
                S.hatW (φ (ψ n)) ((Rz (φ (ψ n))).pd ω) (m (φ (ψ n)) * t0 (φ (ψ n))))
              ((continuous_const_smul _).measurable.comp ((Rz (φ (ψ n))).measurable_hatW _)))
            atTop (𝓝 (lawPM P' (fun ω => w ω 0) (hw 0))) ∧
          ∀ M : ℝ, 0 ≤ M →
            limsup (fun n => (Rz (φ (ψ n))).C.P
                {ω | κw * stNorm ((m (φ (ψ n)))⁻¹ • (((φ (ψ n) : ℕ) : ℝ)⁻¹ • (Rz (φ (ψ n))).X0 ω)) ≤ M})
              atTop ≤ P' {ω | l1 (w ω 0) ≤ M} := by sorry

end FairDiffusionLimit
