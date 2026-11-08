-- Prove2me | Theorems.Thm_AFIsingKS_lemma_3_2
-- name    : AFIsingKS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:23.176807+00:00
-- url     : https://prove2.me/theorems/dfa85c26-c9b3-4d7b-96cf-48d7b1133af8
-- title:
--   Lemma 3.2 — balanced configurations dominate the first moment for real $\beta\ge2\beta_{\mathrm{lb}}$
-- statement:
--   Fix an integer $d\ge 3$. Throughout, $\mathbb E$ is the expectation over $G\sim\mathbb G(n,d)$, the configuration model: a uniformly random perfect matching of the $dn$ sockets $V\times[d]$, contracted to a $d$-regular multigraph; $n$ ranges over the integers with $dn$ even. Spins are $\sigma\in\Sigma_n=\{\pm1\}^n$, $R(\sigma,\sigma')=\langle\sigma,\sigma'\rangle/n$ is the overlap, $\mathcal H_G(\sigma)$ is the number of cut edges, and $\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\}$.
--
--   Let $\beta_{\mathrm{lb}}=-d^{-10}$. For every $\varepsilon>0$ there is $c=c(d,\varepsilon)>0$ such that for all real $\beta\in[2\beta_{\mathrm{lb}},+\infty)$ and $n$ large:
--
--   1. the unbalanced configurations are exponentially negligible,
--   $$\mathbb E[Z_{G,\ge\varepsilon}(\beta)]\le e^{-cn}\,\mathbb E[Z_{G,<\varepsilon}(\beta)];$$
--   2. if $\sigma\in\Sigma_n(\varepsilon)$ is sampled with probability $p(\sigma)\propto\mathbb E[\exp(\beta\mathcal H_G(\sigma))]$, then for all $s\in(0,\varepsilon]$ independent of $n$,
--   $$\Pr_\sigma(|R(\sigma,\mathbf 1)|\ge s)\le2\exp(-cns^2).$$
--
--   This is the input showing that truncating to balanced configurations loses an exponentially small part of the first moment.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - encoding: Z at a real β, the same formula as for complex β → real-valued `cmZltR`, `cmZgeR`, `cmZ2ltR`, `cmZ3ltR`; reason: the inequalities compare real numbers; the casts agree with the complex versions (Remark 4, p.12)
--   - reading: for n sufficiently large, with all other parameters held fixed (p.11) → `∃ N` before `∀ β` on the unbounded range [2β_lb, +∞) in (a); `∀ s, ∃ N` before `∀ β` in (b); reason: β is not among the listed parameters and s is "independent of n"; this is the stronger reading in β
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Lemma 3.2, p.12

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_momentProb
import Definitions.Def_AFIsingKS_cmZR

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Lemma 3.2 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.12): for `β ∈ [2β_lb, +∞)` the balanced configurations dominate the first moment.

**Formalization Note.** "n sufficiently large" (p.11) is `∃ N`, placed before `β` because the paper's
list of fixed parameters omits `β`; in (b) `N` may depend on `s`, which the page calls independent of
`n`. The constant `c` is shared by (a) and (b) and does not depend on `β`. -/
theorem lemma_3_2 (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β : ℝ, 2 * betaLb d ≤ β →
        cmE (fun M : Matching n d => cmZgeR ε M β) ≤
          Real.exp (-c * (n : ℝ)) * cmE (fun M : Matching n d => cmZltR ε M β)) ∧
      (∀ s : ℝ, 0 < s → s ≤ ε → ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β : ℝ, 2 * betaLb d ≤ β →
        firstMomentProb n d ε β (fun σ => s ≤ |overlap σ (allOnes n)|) ≤
          2 * Real.exp (-(c * (n : ℝ) * s ^ 2))) := by sorry

end AFIsingKS
