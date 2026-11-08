-- Prove2me | Theorems.Thm_AFIsingKS_lemma_3_5
-- name    : AFIsingKS.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:10.14836+00:00
-- url     : https://prove2.me/theorems/9d3bc4be-ad1a-4c6f-9f3a-a0fd778104e5
-- title:
--   Lemma 3.5 — the first moment of $Z_{G,<\varepsilon}(\beta)$ on $\mathrm{rect}_+(\delta,\eta_0)$
-- statement:
--   Fix an integer $d\ge 3$. Throughout, $\mathbb E$ is the expectation over $G\sim\mathbb G(n,d)$, the configuration model: a uniformly random perfect matching of the $dn$ sockets $V\times[d]$, contracted to a $d$-regular multigraph; $n$ ranges over the integers with $dn$ even. Spins are $\sigma\in\Sigma_n=\{\pm1\}^n$, $R(\sigma,\sigma')=\langle\sigma,\sigma'\rangle/n$ is the overlap, $\mathcal H_G(\sigma)$ is the number of cut edges, and $\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\}$.
--
--   Let $\delta>0$ and $\varepsilon\in(0,\varepsilon_0)$, with $\varepsilon_0=\varepsilon_0(d,\delta)$. There is $\eta_0=\eta_0(d,\delta,\varepsilon)>0$ such that for all $\beta=E+i\eta\in\mathrm{rect}_+(\delta,\eta_0)$,
--   $$\mathbb E[Z_{G,<\varepsilon}(\beta)]=(1+o_n(1))\sqrt{\frac{1+e^\beta}{d(e^\beta-1)+2}}\cdot2^n\Big(\frac{1+e^\beta}{2}\Big)^{dn/2},$$
--   with the branch of the square root analytic on the complement of the negative real line. Moreover, for any $c>0$ there is $\eta_0=\eta_0(d,\delta,\varepsilon,c)>0$ such that for all $\beta=E+i\eta\in\mathrm{rect}_+(\delta,\eta_0)$ and $n$ large,
--   $$\big|\mathbb E[Z_{G,<\varepsilon}(\beta)]\big|\ge e^{-cn}\,\mathbb E[Z_{G,<\varepsilon}(E)].$$
--
--   In particular the first moment has no zeros on the rectangle, which is what makes normalizing by it possible.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - encoding: Z at a real β, the same formula as for complex β → real-valued `cmZltR`, `cmZgeR`, `cmZ2ltR`, `cmZ3ltR`; reason: the inequalities compare real numbers; the casts agree with the complex versions (Remark 4, p.12)
--   - reading: (1 + o_n(1)) for all β ∈ rect₊(δ, η₀) → for every τ > 0, `∃ N, ∀ n ≥ N, Even (n * d) → ∀ β ∈ rectPlus d δ η₀`, ‖𝔼Z − main‖ ≤ τ‖main‖; the second display also has N before β; reason: the proof of Theorem 3.1 uses the estimate uniformly in β (pp.15–18); this is the stronger reading
--   - reading: ε₀ = ε₀(d, δ), the function set in Lemma 3.9 (p.11) → this item carries its own `∃ ε₀ ∈ (0,1)`; reason: the page fixes ε₀ only inside proofs; every item holds for all ε < ε₀, so the minimum of the items’ ε₀ gives one common value
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Lemma 3.5, p.13

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_cmZ
import Definitions.Def_AFIsingKS_cmZR
import Definitions.Def_AFIsingKS_firstMomentMain

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Lemma 3.5 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.13): the first-moment asymptotic on `rect₊(δ, η₀)`, and the lower bound by the first
moment at the real part.

**Formalization Note.** `(1 + o_n(1))` is uniform over `β ∈ rect₊(δ, η₀)`: for every `τ > 0` and large
`n`, `‖𝔼Z − main‖ ≤ τ ‖main‖`. The `η₀` of the second clause depends on `c`, as printed. -/
theorem lemma_3_5 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ τ : ℝ, 0 < τ → ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ rectPlus d δ η₀,
        ‖cmE (fun M : Matching n d => cmZlt ε M β) - firstMomentMain d n β‖ ≤
          τ * ‖firstMomentMain d n β‖) ∧
      (∀ c : ℝ, 0 < c → ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ rectPlus d δ η₀,
        Real.exp (-c * (n : ℝ)) * cmE (fun M : Matching n d => cmZltR ε M β.re) ≤
          ‖cmE (fun M : Matching n d => cmZlt ε M β)‖) := by sorry

end AFIsingKS
