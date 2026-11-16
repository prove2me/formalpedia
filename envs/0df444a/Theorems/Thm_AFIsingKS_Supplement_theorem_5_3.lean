-- Prove2me | Theorems.Thm_AFIsingKS_Supplement_theorem_5_3
-- name    : AFIsingKS.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:23:53.912206+00:00
-- url     : https://prove2.me/theorems/004c1a17-8820-4536-a5fb-bfa6111029f2
-- title:
--   Theorem 5.3, p.36 — bounded moments of the explicit $A_{L,m}$
-- statement:
--   Let $d\ge3$, consider the configuration model on $n$ clouds of $d$ sockets with $nd$ even and $N=nd$, and let $M$ be the uniformly random perfect matching of the sockets. Let $A_{L,m}(\beta)$ be the reweighting factor of eq. (62) with
--   $$L=\frac{\log\log N}{\log\log\log N},\qquad m=\frac{\log N}{(\log\log N)^2}.$$
--   For every $0<\eta<1$ there is $\rho=\rho(d,\eta)>0$ such that for every fixed $K>0$ there is a constant $C=C(K,d,\eta)>0$ with
--   $$\mathbb E\big[|A_{L,m}(\beta)|^K\big]\le C$$
--   for all $\beta\in\mathbb C$ with $\operatorname{dist}(\beta,[0,(1-\eta)\beta_{\mathrm{KS}}])<\rho$ and all $n$.
--
--   This is item (R2) of Theorem 3.6 for the explicit reweighting $A_{L,m}$: the reweighting factor has bounded moments of every order, so it does not distort probabilities by more than a constant power.
--
--
--   Differences from the source:
--   - encoding: L = log log N / log log log N and m = log N/(log log N)², with L, m ∈ ℕ (p.36) → ⌊log log N / log log log N⌋₊ and ⌊log N/(log log N)²⌋₊ (`cutoffL`, `cutoffM`); reason: L only bounds k ∈ {1,…,L} and m only bounds the natural number |Γ|, so the floors select exactly the same terms of eq. (62)
--   - reading: there exists C = C(K,d,η) > 0 such that for all β in the neighbourhood, 𝔼[|A_{L,m}(β)|^K] ≤ C (n implicit) → ∃ ρ > 0, ∀ K > 0, ∃ C > 0, ∀ n with nd even, ∀ β with dist(β,[0,(1−η)β_KS]) < ρ: 𝔼|A_{L,m}(β)|^K ≤ C; reason: the page prints no threshold in n; for each fixed n the moment is a continuous function of β on the closed neighbourhood (no pole of b_k there for small ρ), so "for all n" and "for n large" are equivalent, and the bound is taken uniform in β (decision 4)
--   - encoding: fixed K > 0, |A|^K → K : ℝ, K > 0, ‖A‖ ^ K as Real.rpow; reason: same instances
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Theorem 5.3, p.36; A_{L,m} eq. (62), p.36

import Mathlib
import Definitions.Def_AFIsingKS_betaKS
import Definitions.Def_AFIsingKS_Supplement_reweight

open scoped Classical
open Set

namespace AFIsingKS.Supplement

/-- Theorem 5.3 (Bounded Moments; Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version,
sha256 2a07c158…), p.36): with `L = log log N / log log log N`, `m = log N / (log log N)^2`, `N = nd`, for
all `0 < η < 1` and all fixed `K > 0` there is `C = C(K, d, η) > 0` such that for all `β` in a sufficiently
small (depending on `d, η`) neighbourhood of `[0, (1 − η) β_KS]`, `𝔼[|A_{L,m}(β)|^K] ≤ C`.

**Formalization Note.** The neighbourhood is the open `ρ`-neighbourhood in `ℂ` of the real segment, with
`ρ = ρ(d, η)` chosen before `K`. `K` is real and `|A|^K` is `Real.rpow`. The bound holds for every `n`
with `nd` even, uniformly in `β` (when `nd` is odd `cmE` is `0`). `L, m` are the rounded-down `cutoffL`,
`cutoffM`. -/
theorem theorem_5_3 (d : ℕ) (hd : 3 ≤ d) (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, Even (n * d) → ∀ β : ℂ,
        Metric.infDist β (((↑) : ℝ → ℂ) '' Icc 0 ((1 - η) * betaKS d)) < ρ →
        cmE (fun M : Matching n d => ‖reweight (cutoffL n d) (cutoffM n d) M β‖ ^ K) ≤ C := by sorry

end AFIsingKS.Supplement
