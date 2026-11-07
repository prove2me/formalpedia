-- Prove2me | Theorems.Thm_DynHaussler_lemma_17
-- name    : DynHaussler.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:12.228069+00:00
-- url     : https://prove2.me/theorems/63a1626e-5043-4b53-957e-d563959dd24b
-- title:
--   Lemma 17 — adaptive low-hit sampling: $\Pr\{\exists\phi: L_\phi\ge B, H_\phi\le q\}\le2(S_r(M)2^qe^{-c_0\gamma B}+e^{-2\gamma T/3})$
-- statement:
--   Let $A\subseteq\{0,1,*\}^Z$ have Littlestone dimension at most an integer $r\ge0$. Let $\xi_1,\dots,\xi_T$ be independent Bernoulli-$\gamma$ bits, $0<\gamma\le1/2$, and let $z_1,\dots,z_T$ be a **predictable input stream**: $z_t$ is a deterministic function of $(\xi_{<t},\omega)$ for an independent auxiliary seed $\omega$ of finite support. For $\phi\in A$ put
--   $$
--   L_\phi=\sum_{t=1}^T\mathbf 1\{\phi(z_t)=1\},\qquad H_\phi=\sum_{t=1}^T\xi_t\,\mathbf 1\{\phi(z_t)\neq0\}. \tag{43}
--   $$
--   Let $q\ge0$ and $B\ge2q$ satisfy $\gamma B\ge16\log2$. With $M=\lceil4\gamma T\rceil$ and $c_0=\log(3/2)/4$,
--   $$
--   \Pr\{\exists\phi\in A: L_\phi\ge B,\ H_\phi\le q\}\le2\Bigl(S_r(M)\,2^q e^{-c_0\gamma B}+e^{-2\gamma T/3}\Bigr). \tag{44}
--   $$
--
--   The bound is uniform over the whole class $A$ even though the inputs react to the earlier sampling choices; it is the probabilistic ingredient of the proof of Proposition 2.
--
--   **Formalization Note** The seed ranges over a finite type with nonnegative weights summing to one, and the probability is the explicit finite sum over seeds and bit vectors of the product weights times the indicator of the event. The class $A$ is arbitrary; $q$, $B$ are real, $\log$ is the natural logarithm and $2^q$ a real power.
--
--   Differences from the source:
--   - encoding: an independent auxiliary seed ω of finite support, and Pr → a finite type Ω with weights μ ≥ 0 summing to 1, and the explicit sum Σ_ω Σ_ξ μ(ω) ∏_t γ^{ξ_t}(1−γ)^{1−ξ_t} 1[event]; reason: a finitely supported law is a law on its finite support; the bits are independent of the seed
--   - encoding: z_t a deterministic function of (ξ_{<t}, ω) → z t (ξ_{<t}) ω with ξ_{<t} = NondualOpt.histPrefix ξ t; reason: 0-based rounds; same streams
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 17, Eqs. (43)–(44), p.23 (PDF p.25); "Order of information", p.23

import Mathlib
import Definitions.Def_DynHaussler_partialLdim
import Definitions.Def_DynHaussler_sCount

set_option autoImplicit false

namespace DynHaussler

open Classical in
/-- **Lemma 17 (Adaptive low-hit sampling).** Let `A ⊆ {0,1,∗}^Z` have Littlestone dimension at most
an integer `r ≥ 0`. Let `z_1, …, z_T` be a predictable input stream for independent Bernoulli-`γ`
bits `ξ_1, …, ξ_T`, where `0 < γ ≤ 1/2`. For each `ϕ ∈ A`, define
`L_ϕ = ∑_t 1{ϕ(z_t) = 1}` and `H_ϕ = ∑_t ξ_t 1{ϕ(z_t) ≠ 0}` (Eq. (43)). Let `q ≥ 0` and `B ≥ 2q`
satisfy `γB ≥ 16 log 2`. With `M = ⌈4γT⌉` and `c_0 = log(3/2)/4`,
`Pr{∃ ϕ ∈ A : L_ϕ ≥ B, H_ϕ ≤ q} ≤ 2 (S_r(M) 2^q e^{−c_0 γ B} + e^{−2γT/3})` (Eq. (44)).
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 17, Eqs. (43)–(44), p.23 (PDF p.25); "Order of information", p.23.

**Formalization Note** The predictable input stream is `z t (ξ_{<t}) ω`: the input of round `t` is a
deterministic function of the earlier sampling bits `ξ_{<t}` (`NondualOpt.histPrefix ξ t`) and an
auxiliary seed `ω`. The seed has finite support: it ranges over a finite type `Ω` with weights
`μ ω ≥ 0` summing to `1`, independent of the bits. The probability is the explicit finite sum
`∑_ω ∑_ξ μ(ω) ∏_t γ^{ξ_t}(1 − γ)^{1−ξ_t} · 1[event]` over `ξ ∈ {0,1}^T` (`Bool`, `true` = 1). The
class `A` is arbitrary (not assumed finite). `q` and `B` are real, counts are cast to `ℝ`, `log`
is the natural logarithm, `⌈·⌉` is `Nat.ceil`, and `2^q` is `Real.rpow`. -/
theorem lemma_17 {Z : Type*} (A : Set (Z → Option Bool)) (r : ℕ) (hA : partialLdim A ≤ r)
    (T : ℕ) (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 2)
    {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (z : (t : Fin T) → (Fin t → Bool) → Ω → Z)
    (q B : ℝ) (hq : 0 ≤ q) (hB : 2 * q ≤ B) (hγB : 16 * Real.log 2 ≤ γ * B) :
    (∑ ω, ∑ ξ : Fin T → Bool, μ ω * (∏ t, if ξ t then γ else 1 - γ) *
      (if ∃ ϕ ∈ A,
          B ≤ ((Finset.univ.filter
            (fun t => ϕ (z t (NondualOpt.histPrefix ξ t) ω) = some true)).card : ℝ) ∧
          ((Finset.univ.filter (fun t => ξ t = true ∧
            ϕ (z t (NondualOpt.histPrefix ξ t) ω) ≠ some false)).card : ℝ) ≤ q
        then (1 : ℝ) else 0)) ≤
      2 * ((sCount r (Nat.ceil (4 * γ * T)) : ℝ) * (2 : ℝ) ^ q *
          Real.exp (-(Real.log (3 / 2) / 4) * γ * B) + Real.exp (-(2 * γ * T / 3))) := by sorry

end DynHaussler
