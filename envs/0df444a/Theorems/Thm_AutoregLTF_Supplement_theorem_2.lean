-- Prove2me | Theorems.Thm_AutoregLTF_Supplement_theorem_2
-- name    : AutoregLTF.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:56:19.526611+00:00
-- url     : https://prove2.me/theorems/280eb2ab-d665-4c7b-9902-7b3251547e45
-- title:
--   Theorem 2 — logistic autoregressive generators shatter $2^{cd}$ prompts with a horizon $T\le2^{2^{Cd}}$
-- statement:
--   Let $\mathcal H_{d,T}$ be the majority class of logistic autoregressive generators with $d$-token window and horizon $T$: for weights $w\in\mathbb R^d$ and bias $b\in\mathbb R$, a prompt $x\in\{0,1\}^d$ is labeled $1$ exactly when $q^{(T)}_{w,b}(x)=\Pr(Z_T=1\mid x)>1/2$, where the tokens are drawn by $\Pr(Z_t=1\mid Z_{1-d},\dots,Z_{t-1})=\sigma(b+\sum_{\ell=1}^d w_\ell Z_{t-\ell})$ with $\sigma(u)=1/(1+e^{-u})$.
--
--   **Theorem 2.** There are constants $c,C>0$ and $d_0$ such that for every $d\ge d_0$ there is an integer $T$ with
--
--   $$1\le T\le 2^{2^{Cd}}\qquad\text{and}\qquad \mathrm{VCdim}(\mathcal H_{d,T})\ge 2^{cd}.$$
--
--   The constants $c$, $C$, $d_0$ are absolute; the horizon $T$ depends on $d$ only, not on the labeling to be realized. In contrast to the deterministic class $\mathcal F_{d,T}$, whose VC dimension is $O(d^2)$ for every $T$, the majority predictions of the canonical logistic generator shatter exponentially many prompts; in particular the real-valued class $\{q^{(T)}_{w,b}\}$ has pseudo-dimension $2^{\Omega(d)}$ for some $T$.
--
--   **Formalization Note** $c$ and $C$ are real, and $2^{cd}$, $2^{2^{Cd}}$ are real powers. The VC dimension is the published `QAlgorithms.Learning.vcDimSet` (a supremum in $\mathbb N\cup\{\infty\}$ of shattered set sizes); because it is a natural number or $\infty$, $\mathrm{VCdim}\ge 2^{cd}$ is stated equivalently as $\lceil 2^{cd}\rceil\le\mathrm{VCdim}$.
--
--   Differences from the source:
--   - reading: an integer T → a natural number T with 1 ≤ T; reason: T is the horizon of the process (2), which runs for 1 ≤ t ≤ T, and the proof's T_m = (K−1)p + 1 + π(out,2) is at least 1; requiring 1 ≤ T is the stronger reading of the existential
--   - encoding: VCdim(H_{d,T}) ≥ 2^{cd} → ⌈2^{cd}⌉₊ ≤ vcDimSet (majCls d T) in ℕ∞; reason: the VC dimension is a natural number or ∞, so the two are equivalent
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Theorem 2, p.2 (PDF p.2); proof in §5, pp.14–20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_AutoregLTF_Supplement_logisticGen

namespace AutoregLTF.Supplement

/-- **Theorem 2**, p.2 (PDF p.2; proof §5, pp.14–20).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"There are constants `c, C > 0` and `d_0` such that for every `d ≥ d_0` there is an integer
`T ≤ 2^{2^{Cd}}` for which `VCdim(H_{d,T}) ≥ 2^{cd}`."

`H_{d,T}` is the majority class (3) of the logistic autoregressive generators (2) with real weights
`w ∈ ℝ^d` and real bias `b`.

**Formalization Note.** `c, C` are real and the powers `2^{cd}`, `2^{2^{Cd}}` are real powers. The
VC dimension is `QAlgorithms.Learning.vcDimSet` (in `ℕ∞`); since it is a natural number or `⊤`,
`VCdim(H_{d,T}) ≥ 2^{cd}` is equivalent to `⌈2^{cd}⌉ ≤ VCdim(H_{d,T})`. The horizon `T` is a natural
number with `1 ≤ T` (the process (2) runs for `1 ≤ t ≤ T`), and it depends on `d` only. -/
theorem theorem_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ T : ℕ, 1 ≤ T ∧ (T : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (C * d)) ∧
        ((⌈(2 : ℝ) ^ (c * d)⌉₊ : ℕ) : ℕ∞) ≤ QAlgorithms.Learning.vcDimSet (majCls d T) := by sorry

end AutoregLTF.Supplement
