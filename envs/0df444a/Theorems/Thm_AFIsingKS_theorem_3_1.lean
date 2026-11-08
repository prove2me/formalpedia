-- Prove2me | Theorems.Thm_AFIsingKS_theorem_3_1
-- name    : AFIsingKS.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:13.717377+00:00
-- url     : https://prove2.me/theorems/ace6bcd3-a358-465d-92ad-5ace7be95517
-- title:
--   Theorem 3.1 — under the configuration model, $Z_G$ is zero-free on $\mathrm{rect}(\delta,\eta_0)$ with high probability
-- statement:
--   For every integer $d\ge3$ and $\delta>0$ there is $\eta_0=\eta_0(d,\delta)>0$ such that for $G\sim\mathbb G(n,d)$,
--   $$\Pr\{Z_G(\beta)\text{ is zero-free on }\mathrm{rect}(\delta,\eta_0)\}=1-o_n(1),$$
--   where $\mathrm{rect}(\delta,\eta_0)=\{E+i\eta:E\in[-d^{-10},\beta_{\mathrm{KS}}(d)-\delta],\ \eta\in[-\eta_0,\eta_0]\}$, $Z_G(\beta)=\sum_\sigma\exp(\beta\mathcal H_G(\sigma))$, and $n\to\infty$ along the integers with $dn$ even.
--
--   This is the configuration-model form of the main theorem, and it directly implies Theorem 1.2.
--
--   Differences from the source:
--   - encoding: expectation and probability over G ∼ G(n,d), spins ±1 → averages over `Matching n d` (pairings, i.e. fixed-point-free involutions, of `Fin n × Fin d`), spins `Fin n → Bool`; reason: finite encodings of the same objects, same instances
--   - encoding: 1 − o_n(1) as n → ∞ → `Tendsto` to 1 along `atTop ⊓ 𝓟 {n | Even (n * d)}`; reason: the configuration model exists only for dn even
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Theorem 3.1, p.11

import Mathlib
import Definitions.Def_AFIsingKS_rect
import Definitions.Def_AFIsingKS_cmZ

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Theorem 3.1 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.11): under the configuration model, with probability `1 − o_n(1)` the partition function
is zero-free on `rect(δ, η₀)`.

**Formalization Note.** `δ` is additive (`β_KS − δ`) here, unlike in Theorem 1.2. The limit runs along the `n`
with `n * d` even, the only `n` with perfect matchings. -/
theorem theorem_3_1 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      Tendsto (fun n => cmProb (fun M : Matching n d => ∀ β ∈ rect d δ η₀, cmZ M β ≠ 0))
        (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1) := by sorry

end AFIsingKS
