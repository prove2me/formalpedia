-- Prove2me | Theorems.Thm_AFIsingKS_corollary_3_8
-- name    : AFIsingKS.corollary_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:15:57.189983+00:00
-- url     : https://prove2.me/theorems/5485479c-4605-46e1-a0b5-19c396c1579d
-- title:
--   Corollary 3.8 — unbalanced configurations are negligible for complex $\beta\in\mathrm{rect}_+(\delta,\eta_0)$
-- statement:
--   Fix an integer $d\ge 3$. Throughout, $\mathbb E$ is the expectation over $G\sim\mathbb G(n,d)$, the configuration model: a uniformly random perfect matching of the $dn$ sockets $V\times[d]$, contracted to a $d$-regular multigraph; $n$ ranges over the integers with $dn$ even. Spins are $\sigma\in\Sigma_n=\{\pm1\}^n$, $R(\sigma,\sigma')=\langle\sigma,\sigma'\rangle/n$ is the overlap, $\mathcal H_G(\sigma)$ is the number of cut edges, and $\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\}$.
--
--   Let $\delta>0$ and $\varepsilon\in(0,\varepsilon_0)$, with $\varepsilon_0=\varepsilon_0(d,\delta)$. There are $c=c(d,\delta,\varepsilon)>0$ and $\eta_0=\eta_0(d,\delta,\varepsilon)>0$ such that for all $\beta\in\mathrm{rect}_+(\delta,\eta_0)$ and $n$ large,
--   $$\mathbb E[|Z_{G,\ge\varepsilon}(\beta)|]\le e^{-cn}\big|\mathbb E[Z_{G,<\varepsilon}(\beta)]\big|.$$
--
--   It extends Lemma 3.2 (a) to the complex strip.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - reading: for n sufficiently large, with all other parameters held fixed (p.11) → `∃ N, ∀ n ≥ N, Even (n * d) → ∀ β in the range`, with N uniform in β; reason: β is not among the listed parameters and the proof of Theorem 3.1 takes suprema over β (pp.15–18); this is the stronger reading
--   - reading: ε₀ = ε₀(d, δ), the function set in Lemma 3.9 (p.11) → this item carries its own `∃ ε₀ ∈ (0,1)`; reason: the page fixes ε₀ only inside proofs; every item holds for all ε < ε₀, so the minimum of the items’ ε₀ gives one common value
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Corollary 3.8, p.14

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_cmZ

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Corollary 3.8 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.14): the extension of Lemma 3.2 (a) to `β ∈ rect₊(δ, η₀)`. -/
theorem corollary_3_8 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∃ c : ℝ, 0 < c ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
      ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ rectPlus d δ η₀,
        cmE (fun M : Matching n d => ‖cmZge ε M β‖) ≤
          Real.exp (-c * (n : ℝ)) * ‖cmE (fun M : Matching n d => cmZlt ε M β)‖ := by sorry

end AFIsingKS
