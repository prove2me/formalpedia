-- Prove2me | Theorems.Thm_AFIsingKS_theorem_3_6
-- name    : AFIsingKS.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:03.685928+00:00
-- url     : https://prove2.me/theorems/0ba29ef0-5f72-47af-ab86-c99021d381df
-- title:
--   Theorem 3.6 — a reweighting factor makes the second moment match the squared first moment
-- statement:
--   Fix an integer $d\ge 3$. Throughout, $\mathbb E$ is the expectation over $G\sim\mathbb G(n,d)$, the configuration model: a uniformly random perfect matching of the $dn$ sockets $V\times[d]$, contracted to a $d$-regular multigraph; $n$ ranges over the integers with $dn$ even. Spins are $\sigma\in\Sigma_n=\{\pm1\}^n$, $R(\sigma,\sigma')=\langle\sigma,\sigma'\rangle/n$ is the overlap, $\mathcal H_G(\sigma)$ is the number of cut edges, and $\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\}$.
--
--   There is a function $A_G(\beta)$ with the following properties.
--
--   1. **(R1)** For all realizations of $G$, $\beta\mapsto A_G(\beta)$ is complex analytic, with $A_G(0)=1$.
--
--   Moreover, let $\delta>0$ and $\varepsilon\in(0,\varepsilon_0)$, with $\varepsilon_0=\varepsilon_0(d,\delta)$. There is $\eta_0=\eta_0(d,\delta,\varepsilon)>0$ such that:
--
--   2. **(R2)** for all $K>0$ there is $C=C(d,\delta,\varepsilon,K)>0$ with $\ \sup_{\beta\in\mathrm{rect}_+(\delta,\eta_0)}\mathbb E[|A_G(\beta)|^K]\le C$;
--   3. **(R3)**
--   $$\sup_{\beta\in\mathrm{rect}_+(\delta,\eta_0)}\left|\frac{\mathbb E[Z^{(2)}_{G,<\varepsilon}(\beta)|A_G(\beta)|^2]}{|\mathbb E[Z_{G,<\varepsilon}(\beta)]|^2}-1\right|=o_n(1).$$
--
--   $A_G$ is the reweighting factor used to run Jensen's formula on the reweighted partition function.
--
--   **Formalization Note** $A$ may depend on $n$ and on the matching, and is chosen before $\delta$ and $\varepsilon$.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - reading: "complex analytic" in (R1), no domain printed → analytic on the strip |Im β| < π/2; reason: Lemma 5.1, p.36, the paper’s own restatement of (R1), gives this strip; the paper’s A has poles at Im β = ±π, so "entire" is not meant
--   - reading: n sufficiently large in (R2); sup = o_n(1) in (R3) → `∃ N` before `∀ β ∈ rectPlus d δ η₀` in (R2) and, for every τ > 0, in (R3); reason: (R3) prints the sup over β; n large is the convention of p.11
--   - reading: ε₀ = ε₀(d, δ), the function set in Lemma 3.9 (p.11) → this item carries its own `∃ ε₀ ∈ (0,1)`; reason: the page fixes ε₀ only inside proofs; every item holds for all ε < ε₀, so the minimum of the items’ ε₀ gives one common value
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Theorem 3.6, p.13; domain of (R1) from Lemma 5.1, p.36

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_cmZ

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Theorem 3.6 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.13): a reweighting factor `A_G(β)`, analytic with `A_G(0) = 1`, with bounded moments,
which makes the near-orthogonal second moment match the squared first moment.

**Formalization Note.** `A` may depend on `n` and the matching, but it is chosen before `δ` and `ε`, as
printed. "Complex analytic" in (R1) has no printed domain; the paper's own restatement, Lemma 5.1 (p.36),
gives the strip `|Im β| < π/2`, which contains `rect₊(δ, η₀)` for `η₀ < π/2`. In (R3) a zero denominator
would make the quotient `0` and the distance to `1` equal `1`, so (R3) cannot hold vacuously. -/
theorem theorem_3_6 (d : ℕ) (hd : 3 ≤ d) :
    ∃ A : (n : ℕ) → Matching n d → ℂ → ℂ,
      (∀ n (M : Matching n d),
        AnalyticOnNhd ℂ (A n M) {β | |β.im| < Real.pi / 2} ∧ A n M 0 = 1) ∧
      ∀ δ : ℝ, 0 < δ → ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∃ η₀ : ℝ, 0 < η₀ ∧
        (∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ rectPlus d δ η₀,
          cmE (fun M : Matching n d => ‖A n M β‖ ^ K) ≤ C) ∧
        (∀ τ : ℝ, 0 < τ → ∃ N : ℕ, ∀ n ≥ N, Even (n * d) → ∀ β ∈ rectPlus d δ η₀,
          ‖cmE (fun M : Matching n d => cmZ2lt ε M β * ((‖A n M β‖ ^ 2 : ℝ) : ℂ)) /
                ((‖cmE (fun M : Matching n d => cmZlt ε M β)‖ ^ 2 : ℝ) : ℂ) - 1‖ ≤ τ) := by sorry

end AFIsingKS
