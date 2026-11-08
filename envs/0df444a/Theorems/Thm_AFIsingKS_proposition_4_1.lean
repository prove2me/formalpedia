-- Prove2me | Theorems.Thm_AFIsingKS_proposition_4_1
-- name    : AFIsingKS.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:17:14.219733+00:00
-- url     : https://prove2.me/theorems/8b4f0ec4-0236-4fd0-a17c-0ded82d476ec
-- title:
--   Proposition 4.1 — overlap concentration carries all but $e^{-cn}$ of the moments
-- statement:
--   Fix an integer $d\ge 3$. Throughout, $\mathbb E$ is the expectation over $G\sim\mathbb G(n,d)$, the configuration model: a uniformly random perfect matching of the $dn$ sockets $V\times[d]$, contracted to a $d$-regular multigraph; $n$ ranges over the integers with $dn$ even. Spins are $\sigma\in\Sigma_n=\{\pm1\}^n$, $R(\sigma,\sigma')=\langle\sigma,\sigma'\rangle/n$ is the overlap, $\mathcal H_G(\sigma)$ is the number of cut edges, and $\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\}$.
--
--   Let $\delta>0$ and $\varepsilon\in(0,\varepsilon_0)$, with $\varepsilon_0=\varepsilon_0(d,\delta)$. There is $c=c(d,\delta,\varepsilon)>0$ such that for all real $\beta\in[2\beta_{\mathrm{lb}},\beta_{\mathrm{KS}}-\delta]$ and $n$ large, with $\mathcal O_{\beta,c}$ and $\mathcal O^{(2)}_{\beta,c}$ the events (22) and (24),
--   $$\mathbb E[\mathbf 1\{G\notin\mathcal O_{\beta,c}\}Z_{G,<\varepsilon}(\beta)]\le e^{-cn}\,\mathbb E[Z_{G,<\varepsilon}(\beta)]$$
--   and
--   $$\sum_{\sigma,\sigma'\in\Sigma_n(\varepsilon)}\mathbf 1\{|R(\sigma,\sigma')|<\varepsilon\}\,\mathbb E\big[\mathbf 1\{(\sigma',G)\notin\mathcal O^{(2)}_{\beta,c}\}e^{\beta\mathcal H_G(\sigma)+\beta\mathcal H_G(\sigma')}\big]\le e^{-cn}\,\mathbb E[Z^{(2)}_{G,<\varepsilon}(\beta)].$$
--
--   It is the variant of Theorem 3.3 and Corollary 3.4 from which those results are derived.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - encoding: Z at a real β, the same formula as for complex β → real-valued `cmZltR`, `cmZgeR`, `cmZ2ltR`, `cmZ3ltR`; reason: the inequalities compare real numbers; the casts agree with the complex versions (Remark 4, p.12)
--   - reading: for n sufficiently large, with all other parameters held fixed (p.11) → `∃ N, ∀ n ≥ N, Even (n * d) → ∀ β in the range`, with N uniform in β; reason: β is not among the listed parameters and the proof of Theorem 3.1 takes suprema over β (pp.15–18); this is the stronger reading
--   - reading: ε₀ = ε₀(d, δ), the function set in Lemma 3.9 (p.11) → this item carries its own `∃ ε₀ ∈ (0,1)`; reason: the page fixes ε₀ only inside proofs; every item holds for all ε < ε₀, so the minimum of the items’ ε₀ gives one common value
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Proposition 4.1, p.19, eqs. (22)–(25), with the standing assumptions of Section 4, p.18

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_gibbsProb

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Proposition 4.1 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.19): graphs on which two Gibbs replicas are not nearly orthogonal contribute
at most an `e^{−cn}` fraction of the first and of the near-orthogonal second moment (eqs. (22)–(25)).

**Formalization Note.** The same `c` appears in the events `overlapEvent`, `overlapEvent2` and in the
bounds, as printed. The standing assumptions of Section 4 (p.18) are binders. -/
theorem proposition_4_1 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
      ∀ β ∈ Icc (2 * betaLb d) (betaKS d - δ),
        cmE (fun M : Matching n d => if overlapEvent ε c β M then 0 else cmZltR ε M β) ≤
            Real.exp (-c * (n : ℝ)) * cmE (fun M : Matching n d => cmZltR ε M β) ∧
        (∑ σ ∈ balanced n ε, ∑ σ' ∈ balanced n ε,
            if |overlap σ σ'| < ε then
              cmE (fun M : Matching n d =>
                if overlapEvent2 ε c β σ' M then 0
                else Real.exp (β * (cmCut M σ : ℝ) + β * (cmCut M σ' : ℝ)))
            else 0) ≤
          Real.exp (-c * (n : ℝ)) * cmE (fun M : Matching n d => cmZ2ltR ε M β) := by sorry

end AFIsingKS
