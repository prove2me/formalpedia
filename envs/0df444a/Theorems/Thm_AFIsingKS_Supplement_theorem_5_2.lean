-- Prove2me | Theorems.Thm_AFIsingKS_Supplement_theorem_5_2
-- name    : AFIsingKS.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:23:18.011214+00:00
-- url     : https://prove2.me/theorems/36a53017-5d86-418f-9a5b-c778279ae9af
-- title:
--   Theorem 5.2, p.36 — reweighted second moment for the explicit $A_{L,m}$
-- statement:
--   Let $d\ge3$, consider the configuration model on $n$ clouds of $d$ sockets with $nd$ even and $N=nd$, and let $M$ be the uniformly random perfect matching of the sockets. For $\varepsilon>0$ let $Z_{M,<\varepsilon}(\beta)$ be the partition function restricted to balanced configurations ($|R(\sigma,\mathbf 1)|<\varepsilon$) and $Z^{(2)}_{M,<\varepsilon}(\beta)=\sum e^{\beta H_M(\sigma^1)+\bar\beta H_M(\sigma^2)}$ over balanced pairs with $|R(\sigma^1,\sigma^2)|<\varepsilon$. Let $A_{L,m}(\beta)$ be the reweighting factor of eq. (62) with
--   $$L=\frac{\log\log N}{\log\log\log N},\qquad m=\frac{\log N}{(\log\log N)^2}.$$
--   For every $0<\eta<1$ there is $\rho=\rho(d,\eta)>0$ such that, for all sufficiently small $\varepsilon>0$ and all $\beta\in\mathbb C$ with $\operatorname{dist}(\beta,[0,(1-\eta)\beta_{\mathrm{KS}}])<\rho$,
--   $$\frac{\mathbb E_M\big[Z^{(2)}_{M,<\varepsilon}(\beta)\,|A_{L,m}(\beta)|^2\big]}{\big|\mathbb E_M[Z_{M,<\varepsilon}(\beta)]\big|^2}=1\pm o_n(1),$$
--   where the $o_n(1)$ may depend on $d,\varepsilon,\eta$ but not on $\beta$.
--
--   This is item (R3) of Theorem 3.6 for the explicit reweighting $A_{L,m}$: after reweighting by short cycles, the second moment of the truncated partition function matches the square of its first moment, which is the input to the zero-freeness argument.
--
--
--   Differences from the source:
--   - encoding: L = log log N / log log log N and m = log N/(log log N)², with L, m ∈ ℕ (p.36) → ⌊log log N / log log log N⌋₊ and ⌊log N/(log log N)²⌋₊ (`cutoffL`, `cutoffM`); reason: L only bounds k ∈ {1,…,L} and m only bounds the natural number |Γ|, so the floors select exactly the same terms of eq. (62)
--   - reading: all β within a sufficiently small constant (depending on d, η) neighborhood of [0,(1−η)β_KS], all sufficiently small ε > 0, ratio = 1 ± o_n(1) with constants depending on d, ε, η → ∃ ρ > 0, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), ∀ τ > 0, ∃ N₀, ∀ n ≥ N₀ with nd even, ∀ β with dist(β,[0,(1−η)β_KS]) < ρ: ‖ratio − 1‖ ≤ τ; reason: the printed order puts the neighbourhood (depending on d, η) before ε; ε₀ and the o_n(1) are taken uniform in β, the stronger reading and the base mission convention (paper.md decision 4)
--   - encoding: = 1 ± o_n(1) → ‖ratio − 1‖ ≤ τ for every τ > 0 and n large, the ratio computed in ℂ; reason: definition of o_n(1); a zero denominator makes the Lean quotient 0, so the bound cannot hold vacuously
--   - encoding: n → ∞ in the configuration model → n with Even (n * d); reason: the configuration model exists only for dn even (p.9)
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Theorem 5.2, p.36; A_{L,m} eq. (62), p.36; Z_{M,<ε}, Z^{(2)}_{M,<ε}, Section 3.1, pp.11–12

import Mathlib
import Definitions.Def_AFIsingKS_betaKS
import Definitions.Def_AFIsingKS_cmZ
import Definitions.Def_AFIsingKS_Supplement_reweight

open scoped Classical
open Set

namespace AFIsingKS.Supplement

/-- Theorem 5.2 (Reweighted Second Moment; Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version,
sha256 2a07c158…), p.36): with `L = log log N / log log log N`, `m = log N / (log log N)^2`, `N = nd`, for
all `0 < η < 1`, all `β` in a sufficiently small (depending on `d, η`) neighbourhood of `[0, (1 − η) β_KS]`
and all sufficiently small `ε > 0`,
`𝔼_M[Z^{(2)}_{M,<ε}(β) |A_{L,m}(β)|²] / |𝔼_M Z_{M,<ε}(β)|² = 1 ± o_n(1)`.

**Formalization Note.** The neighbourhood is the open `ρ`-neighbourhood in `ℂ` of the real segment, with
`ρ = ρ(d, η)` chosen before `ε`; the threshold `ε₀` is uniform in `β`, and the `o_n(1)` is uniform in `β`
and may depend on `d, ε, η` (∃ `N₀` before ∀ `β`). `L, m` are the rounded-down `cutoffL`, `cutoffM`.
A zero denominator would make the quotient `0` and the distance to `1` equal to `1`, so the bound cannot
hold vacuously. -/
theorem theorem_5_2 (d : ℕ) (hd : 3 ≤ d) (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ τ : ℝ, 0 < τ →
      ∃ N₀ : ℕ, ∀ n ≥ N₀, Even (n * d) → ∀ β : ℂ,
        Metric.infDist β (((↑) : ℝ → ℂ) '' Icc 0 ((1 - η) * betaKS d)) < ρ →
        ‖cmE (fun M : Matching n d =>
              cmZ2lt ε M β * ((‖reweight (cutoffL n d) (cutoffM n d) M β‖ ^ 2 : ℝ) : ℂ)) /
            ((‖cmE (fun M : Matching n d => cmZlt ε M β)‖ ^ 2 : ℝ) : ℂ) - 1‖ ≤ τ := by sorry

end AFIsingKS.Supplement
