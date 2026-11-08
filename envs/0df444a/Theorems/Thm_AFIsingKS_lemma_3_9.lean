-- Prove2me | Theorems.Thm_AFIsingKS_lemma_3_9
-- name    : AFIsingKS.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:11.661254+00:00
-- url     : https://prove2.me/theorems/1f16b6e3-160a-45ac-a929-78978ad81deb
-- title:
--   Lemma 3.9 — replicated moments of $Z_{G,<\varepsilon}$ for real $\beta\in[2\beta_{\mathrm{lb}},\beta_{\mathrm{KS}}-\delta]$
-- statement:
--   Fix an integer $d\ge 3$. Throughout, $\mathbb E$ is the expectation over $G\sim\mathbb G(n,d)$, the configuration model: a uniformly random perfect matching of the $dn$ sockets $V\times[d]$, contracted to a $d$-regular multigraph; $n$ ranges over the integers with $dn$ even. Spins are $\sigma\in\Sigma_n=\{\pm1\}^n$, $R(\sigma,\sigma')=\langle\sigma,\sigma'\rangle/n$ is the overlap, $\mathcal H_G(\sigma)$ is the number of cut edges, and $\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\}$.
--
--   Let $\delta>0$. There is $\varepsilon_0=\varepsilon_0(d,\delta)\in(0,1)$ such that for all $\varepsilon\in(0,\varepsilon_0)$ the following hold for all real $\beta\in[2\beta_{\mathrm{lb}},\beta_{\mathrm{KS}}-\delta]$ and $n$ large:
--
--   1. for every $\upsilon>0$, $\ \mathbb E[Z^{(2)}_{G,<\varepsilon}(\beta)]\le e^{\upsilon n}\,\mathbb E[Z_{G,<\varepsilon}(\beta)]^2$;
--   2. there is $c=c(d,\delta,\varepsilon)>0$ such that if $(\sigma,\sigma')\in\Sigma_{n,2}(\varepsilon)$ is sampled with probability $p(\sigma,\sigma')\propto\mathbb E[\exp(\beta\mathcal H_G(\sigma)+\beta\mathcal H_G(\sigma'))]$, then for all $s\in(0,\varepsilon]$ independent of $n$,
--   $$\Pr_{\sigma,\sigma'}\big(\max(|R(\sigma,\mathbf 1)|,|R(\sigma',\mathbf 1)|,|R(\sigma,\sigma')|)\ge s\big)\le6\exp(-ns^2/(2c));$$
--   3. for every $\upsilon>0$, $\ \mathbb E[Z^{(3)}_{G,<\varepsilon}(\beta)]\le e^{\upsilon n}\,\mathbb E[Z_{G,<\varepsilon}(\beta)]^3$.
--
--   These real moments, accurate to leading exponential order, feed the truncation estimates of Section 4.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - encoding: Z at a real β, the same formula as for complex β → real-valued `cmZltR`, `cmZgeR`, `cmZ2ltR`, `cmZ3ltR`; reason: the inequalities compare real numbers; the casts agree with the complex versions (Remark 4, p.12)
--   - reading: for n sufficiently large, with all other parameters held fixed (p.11) → `∃ N, ∀ n ≥ N, Even (n * d) → ∀ β in the range`, with N uniform in β; reason: β is not among the listed parameters and the proof of Theorem 3.1 takes suprema over β (pp.15–18); this is the stronger reading
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Lemma 3.9, p.18, with eqs. (17)–(18)

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_momentProb
import Definitions.Def_AFIsingKS_cmZR

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Lemma 3.9 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.18): replicated moments of the balanced partition function for real
`β ∈ [2β_lb, β_KS − δ]`.

**Formalization Note.** `c` in (b) depends on `d, δ, ε` and not on `υ`, so `∀ υ` is written separately
in (a) and (c). The threshold `N` may depend on `υ`, and in (b) on `s`, but not on `β`. The bound in (b)
has `c` in the denominator, as printed. -/
theorem lemma_3_9 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      (∀ υ : ℝ, 0 < υ → ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ Icc (2 * betaLb d) (betaKS d - δ),
        cmE (fun M : Matching n d => cmZ2ltR ε M β) ≤
          Real.exp (υ * (n : ℝ)) * cmE (fun M : Matching n d => cmZltR ε M β) ^ 2) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 < s → s ≤ ε →
        ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ Icc (2 * betaLb d) (betaKS d - δ),
          secondMomentProb n d ε β (fun σ σ' =>
              s ≤ max (max |overlap σ (allOnes n)| |overlap σ' (allOnes n)|) |overlap σ σ'|) ≤
            6 * Real.exp (-((n : ℝ) * s ^ 2) / (2 * c))) ∧
      (∀ υ : ℝ, 0 < υ → ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ Icc (2 * betaLb d) (betaKS d - δ),
        cmE (fun M : Matching n d => cmZ3ltR ε M β) ≤
          Real.exp (υ * (n : ℝ)) * cmE (fun M : Matching n d => cmZltR ε M β) ^ 3) := by sorry

end AFIsingKS
