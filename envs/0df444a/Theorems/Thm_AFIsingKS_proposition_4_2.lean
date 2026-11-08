-- Prove2me | Theorems.Thm_AFIsingKS_proposition_4_2
-- name    : AFIsingKS.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:17:35.206746+00:00
-- url     : https://prove2.me/theorems/476d7698-f510-4ed7-8762-70152366287b
-- title:
--   Proposition 4.2 — a Gibbs sample is nearly orthogonal to the planted signal
-- statement:
--   Fix an integer $d\ge 3$. Throughout, $\mathbb E$ is the expectation over $G\sim\mathbb G(n,d)$, the configuration model: a uniformly random perfect matching of the $dn$ sockets $V\times[d]$, contracted to a $d$-regular multigraph; $n$ ranges over the integers with $dn$ even. Spins are $\sigma\in\Sigma_n=\{\pm1\}^n$, $R(\sigma,\sigma')=\langle\sigma,\sigma'\rangle/n$ is the overlap, $\mathcal H_G(\sigma)$ is the number of cut edges, and $\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\}$.
--
--   Let $\delta>0$ and $\varepsilon\in(0,\varepsilon_0)$, with $\varepsilon_0=\varepsilon_0(d,\delta)$. There is $c=c(d,\delta,\varepsilon)>0$ such that for all real $\beta\in[2\beta_{\mathrm{lb}},\beta_{\mathrm{KS}}-\delta]$ and $n$ large,
--   $$\mathbb E^{\mathrm{pl}}_\beta\,\mu_{G,\beta,<\varepsilon}(|R(\sigma,\sigma^*)|\ge\varepsilon)\le e^{-cn},\qquad \mathbb E^{\mathrm{pl},2}_\beta\,\mu^{2,\sigma'^*}_{G,\beta,<\varepsilon}(|R(\sigma,\sigma^*)|\ge\varepsilon)\le e^{-cn}.$$
--
--   Here $(\sigma^*,G)$ follows the planted model and $(\sigma^*,\sigma'^*,G)$ the two-replica planted model. The statement says the planted signal cannot be weakly recovered, with an exponentially small failure probability, below the Kesten–Stigum threshold.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - reading: for n sufficiently large, with all other parameters held fixed (p.11) → `∃ N, ∀ n ≥ N, Even (n * d) → ∀ β in the range`, with N uniform in β; reason: β is not among the listed parameters and the proof of Theorem 3.1 takes suprema over β (pp.15–18); this is the stronger reading
--   - reading: ε₀ = ε₀(d, δ), the function set in Lemma 3.9 (p.11) → this item carries its own `∃ ε₀ ∈ (0,1)`; reason: the page fixes ε₀ only inside proofs; every item holds for all ε < ε₀, so the minimum of the items’ ε₀ gives one common value
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Proposition 4.2, p.20, with the standing assumptions of Section 4, p.18

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_gibbsProb
import Definitions.Def_AFIsingKS_plantedE

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Proposition 4.2 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.20): under the planted models, a Gibbs sample is nearly orthogonal to the
planted signal.

**Formalization Note.** The standing assumptions of Section 4 (p.18) are binders: `δ > 0`, the `ε₀` of
the section, `ε ∈ (0, ε₀)`, and a real `β`. -/
theorem proposition_4_2 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
      ∀ β ∈ Icc (2 * betaLb d) (betaKS d - δ),
        plantedE n d ε β (fun σs M => gibbsProb ε β M (fun σ => ε ≤ |overlap σ σs|)) ≤
            Real.exp (-c * (n : ℝ)) ∧
        plantedE2 n d ε β (fun σs σs' M => condProb ε β M σs' (fun σ => ε ≤ |overlap σ σs|)) ≤
            Real.exp (-c * (n : ℝ)) := by sorry

end AFIsingKS
