-- Prove2me | Theorems.Thm_FTPLLinBandit_theorem_13
-- name    : FTPLLinBandit.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:11:08.678095+00:00
-- url     : https://prove2.me/theorems/f2e74e46-ccd7-49ca-b565-eaf1c30311aa
-- title:
--   Theorem 13 — FTPL with any of the nine adaptive perturbations has $\mathrm{Reg}_T(a)=\tilde O((d+Rd^{3/4})\sqrt T)$
-- statement:
--   There are universal constants $C_0>0$ and $k\in\mathbb N$ such that for every $C\ge C_0$ there is a constant $K$ with the following property. Let $d\ge1$, let $A\subseteq\mathbb R^d$ and $\nu$ satisfy Assumption 1 with radii $r,R$, let $x$ be an argmax selection of $A$, and let $T$ be the horizon. Use the parameters (20),
--   $$L=\log\frac{4RT}{r},\qquad\beta=\frac1{2R^2},\qquad\gamma=\frac{4R(L+1)d^{3/4}}{\sqrt T},\qquad N+1=\Big\lceil\frac{Ld}{\beta\gamma}\Big\rceil,$$
--   $G=2R\beta(N+1)$, and the scale (22),
--   $$\lambda=CG^2\cdot\begin{cases}\log^2(RGT)&\text{random-weighting perturbations},\\ 1&\text{elliptical perturbations}.\end{cases}$$
--   Then for random-weighting perturbations with any initializer of Table 2 and any scalar law of Table 3, or for elliptical perturbations with any radial law of Table 4, every run of Algorithm 1 against an adaptive adversary with $|r_t|\le1$ on $A$ satisfies, for every $a\in A$,
--   $$\mathrm{Reg}_T(a)\le K\,\big(d+Rd^{3/4}\big)\sqrt T\,\Big(1+\log\Big(1+\frac{dRT}{r}\Big)\Big)^k,$$
--   that is, $\mathrm{Reg}_T(a)=\tilde O\big((d+Rd^{3/4})\sqrt T\big)$.
--
--   With a barycentric spanner ($R\le4\sqrt d$) this gives $\tilde O(d^{5/4}\sqrt T)$, and with an optimal design ($R=1$) the near-optimal $\tilde O(d\sqrt T)$.
--
--   **Formalization Note** "Assume $\gamma\le1/2$ without loss of generality" is not a hypothesis: every horizon is covered (the proof treats $\gamma>1/2$ by $\mathrm{Reg}_T\le2T$), and the run is defined for every $\gamma$ (for $\gamma\ge1$ it always explores).
--
--   Differences from the source:
--   - reading: Reg_T(a) = Õ((d + Rd^{3/4})√T) with C "a sufficiently large universal constant" → ∃ C₀ > 0, ∃ k, ∀ C ≥ C₀, ∃ K, ∀ instances: Reg_T(a) ≤ K (d + Rd^{3/4}) √T (1 + log(1 + dRT/r))^k; reason: §2, p.3: ≲ is "≤ a universal constant times" and Õ "further hides polylogarithmic factors"; the logarithms of the analysis (L = log(4RT/r), log(RGT), log(dRGT), log(1 + TG²/(dλ))) are polylogarithmic in d, R, T, 1/r; "every C ≥ C₀" is the stronger reading of "sufficiently large", and K may depend on C (Ψ₁(0) grows like √C, Lemma 37)
--   - encoding: N + 1 = ⌈Ld/(βγ)⌉ → N = ⌈Ld/(βγ)⌉₊ − 1; reason: for T ≥ 1 the ceiling is at least 1 (proved in the mission's sanity checks), so N + 1 = ⌈Ld/(βγ)⌉; at T = 0 both sides of the bound are 0
--   - encoding: "Assume γ ≤ 1/2 without loss of generality"; Algorithm 1 takes γ ∈ [0, 1] → no hypothesis on γ; the coin U < γ always explores when γ ≥ 1; reason: the paper's proof covers γ > 1/2 by Reg_T ≤ 2T < 16R(L + 1)d^{3/4}√T for any learner, so every horizon is in the theorem
--   - encoding: e ∼ Bernoulli(γ), explore iff e = 1 → a uniform coin U on [0, 1], explore iff U < γ; reason: same law for γ ∈ [0, 1]
--   - generalization: an adversary that may depend on the past and chooses θ_t, b_t before round t's draws; E_t is conditioning on the history before round t → θ_t, b_t adapted to any filtration 𝓕 with the round-t draws independent of 𝓕_t and 𝓕_{t+1}-measurable; E_t is conditional expectation given 𝓕_t; reason: the history filtration of a deterministic adaptive adversary is an instance; the filtration may also carry the adversary's own randomness
--   - generalization: elliptical sampling Z_t = Σ_t^{1/2} S U → Z_t = B(Σ_t) W with W ∼ P_I and any measurable B with B(Σ)B(Σ)ᵀ = Σ for positive definite Σ; reason: every such factor gives Z_t ∼ P_{Σ_t}; B = Σ^{1/2} with W = SU is the paper's sampler
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: Assumption 1 with the standing d ≥ 1 and Cov(ν) = I/d → IsNormalized (the covariance as the identity ∫⟨u, a⟩² dν = ‖u‖²/d for every u, ν a probability measure with ν Aᶜ = 0) and the hypothesis 1 ≤ d; reason: µ(ν) = 0, so Cov(ν) = E[aaᵀ], and a symmetric matrix is determined by its quadratic form; same instances
--   - encoding: SampleAction draws e, then either a ∼ ν or Z ∼ ρ_t; for random weighting Z = Z′ + Σ ξ_τ θ̂_τ with Z′ ∼ ρ₁ → every call (2N + 2 slots per round, Fin (2N + 2)) draws its coin, X ∼ ν, W ∼ P_I and weights up front and uses what it needs; Z = √λ W + Σ ξ_τ θ̂_τ; reason: √λ W ∼ P_{λI} = ρ₁, and a draw that is not used changes no law; the slots are independent, as the calls of Algorithm 1 are
--   - generalization: Figure 2: "with parameter λ > 0"; horizons T ≥ 1 → no hypothesis λ > 0 and T : ℕ, so λ = 0 (random weighting with RGT = 1) and T = 0 are allowed; reason: for T ≥ 1, λ = 0 forces T = 1 and N = 0, where γ > 1/2 and Reg_T ≤ 2T holds for any learner; at T = 0 both sides are 0; every instance with λ > 0 and T ≥ 1 is the paper's
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 13, Eq. (23), p.14, with the parameters (20) and (22), pp.13–14 (proof Appendix J, p.48)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsNormalized
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_FTPLRun_regret

open MeasureTheory

universe u

namespace FTPLLinBandit

/-- **Theorem 13 (√T regret of FTPL with adaptive perturbations).** Wei, *Follow the Perturbed
Leader for Linear Bandits: √T Regret over General Action Sets*, arXiv:2610.17818, Theorem 13,
Eq. (23), p.14: "Under Assumption 1, use the parameters above. For random-weighting perturbations
with any initializer from Table 2 and any scalar law from Table 3, or for elliptical perturbations
with any radial law from Table 4, Algorithm 1 achieves for every a ∈ A,
Reg_T(a) = Õ((d + Rd^{3/4})√T)", with the parameters (20) and (22), pp.13–14:
"L = log(4RT/r), β = 1/(2R²), γ = 4R(L + 1)d^{3/4}/√T, N + 1 = ⌈Ld/(βγ)⌉. … Define
G = 2Rβ(N + 1). … λ = CG² · {log²(RGT), for random-weighting perturbations; 1, for elliptical
perturbations}, where C is a sufficiently large universal constant."

There are universal constants `C₀ > 0` and `k ∈ ℕ` such that for every `C ≥ C₀` there is a
constant `K` with the following property. For every dimension `d ≥ 1`, every action set `A` with
exploration distribution `ν` satisfying Assumption 1 with radii `r, R`, every argmax selection `x`,
every horizon `T`, each of the nine perturbation schemes `s`, and every run of Algorithm 1 (on any
probability space, against any adaptive adversary with `|r_t| ≤ 1` on `A`) with the parameters
`γ, β, N` of (20) and the scale `λ` of (22) built from `C`, every comparator `a ∈ A` has
`Reg_T(a) ≤ K (d + R d^{3/4}) √T (1 + log(1 + dRT/r))^k`.

**Formalization Note.** `Õ` is read as the paper defines it (§2, p.3: "≲" is "≤ a universal
constant times", and "Õ further hides polylogarithmic factors"): a constant `K` and a power `k`
of a logarithm, both fixed before every instance. The logarithms of the analysis
(`L = log(4RT/r)`, `log(RGT)`, `log(dRGT)`, `log(1 + TG²/(dλ))`) are bounded by constant multiples
of powers of `1 + log(1 + dRT/r)`. "A sufficiently large universal constant C" is read as "every
`C ≥ C₀`"; `K` may depend on `C`. `N` is the natural number `⌈Ld/(βγ)⌉ − 1` (for `T ≥ 1` the
ceiling is at least `1`). "Assume γ ≤ 1/2 without loss of generality" is not a hypothesis: the
statement covers every `T`, and the run is defined for every `γ` (with `γ ≥ 1` it always
explores). Rounds are indexed from `0`; `Real.log`, `Real.sqrt` and real division carry Lean's
conventions at `T = 0` (where both sides vanish). -/
theorem theorem_13 : ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ k : ℕ, ∀ C : ℝ, C₀ ≤ C → ∃ K : ℝ,
    ∀ (d : ℕ), 1 ≤ d → ∀ (A : Set (EuclideanSpace ℝ (Fin d)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))) (r R : ℝ), IsNormalized A ν r R →
    ∀ (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)), IsArgmaxSel A x →
    ∀ (T : ℕ) (s : Scheme) (γ β : ℝ) (N : ℕ) (lam : ℝ),
      γ = 4 * R * (Real.log (4 * R * T / r) + 1) * (d : ℝ) ^ ((3 : ℝ) / 4) / Real.sqrt T →
      β = 1 / (2 * R ^ 2) →
      N = ⌈Real.log (4 * R * T / r) * d / (β * γ)⌉₊ - 1 →
      lam = C * (2 * R * β * ((N : ℝ) + 1)) ^ 2 *
        (match s with
         | .randomWeighting _ _ => Real.log (R * (2 * R * β * ((N : ℝ) + 1)) * T) ^ 2
         | .elliptical _ => 1) →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (run : FTPLRun A ν x s γ β N lam Ω P) (a : EuclideanSpace ℝ (Fin d)), a ∈ A →
      run.regret T a ≤
        K * ((d : ℝ) + R * (d : ℝ) ^ ((3 : ℝ) / 4)) * Real.sqrt T *
          (1 + Real.log (1 + d * R * T / r)) ^ k := by sorry

end FTPLLinBandit
