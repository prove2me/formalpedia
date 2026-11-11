-- Prove2me | Theorems.Thm_DQIShattered_theorem_2_7
-- name    : DQIShattered.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:31:09.554395+00:00
-- url     : https://prove2.me/theorems/a44cd74c-e77d-444c-843f-4f9f7f23c2a1
-- title:
--   Theorem 2.7 — DQI+USD efficiently Gibbs-samples $\mathbb G_{\mathrm{ER}}(N,k,D)$ at every $\beta<\tanh^{-1}(K_*(k)/D)$
-- statement:
--   Fix $k\ge3$, a real $D\ge k$ and $\delta\in(0,1)$, and let $(B,J)\sim\mathbb G_{\mathrm{ER}}(N,k,D)$. Recall $\gamma_{\mathrm{USD}}(k,D)=\frac12-\frac12\sqrt{1-(K_*(k)/D)^2}$, with $K_*(k)$ as in (2.10).
--
--   **(A) Decoding.** For every $\gamma\in[0,\gamma_{\mathrm{USD}}(k,D))$ there is a polynomial-time family of decoder circuits over $\{H,T,\mathrm{CNOT}\}$ that solves the $(B,\gamma,\delta)$-quantum decoding problem with probability $1-o_N(1)$ over $B$.
--
--   **(B) Sampling.** Let $\varepsilon>0$, and let $\beta\ge0$ satisfy
--
--   $$\beta<\beta_{\mathrm{ALG}}(k,D)=\tanh^{-1}\Big(\frac{K_*(k)}{D}\Big).$$
--
--   Set $\gamma=\frac12-\frac12\operatorname{sech}\beta$.
--
--   1. *(DQI)* There is a decoder family as in (A), at this $\gamma$ (its machine reading the digits of $\beta$), with the following property. For every fixed $z_0$, the exact DQI output law $\nu^{\mathrm{DQI}}_{B,J,\beta}$ built from its decoder unitaries is within total variation $\varepsilon$ of $\mu_{\beta,H_{B,J}}$, with probability at least $1-\sqrt\delta/\varepsilon-o_N(1)$ over $(B,J)$.
--   2. *(Efficiently, by DQI)* There is a polynomial-time family of sampler circuits over $\{H,T,\mathrm{CNOT}\}$ that implements this DQI sampler: on every instance its output law is within total variation $\eta_N\to0$ of $\nu^{\mathrm{DQI}}_{B,J,\beta}$ built from the same decoder circuits (with $z_0=(+1,\dots,+1)$). Its output law is within total variation $\varepsilon$ of $\mu_{\beta,H_{B,J}}$, with probability at least $1-\sqrt\delta/\varepsilon-o_N(1)$ over $(B,J)$.
--
--   Shattering sets in at $(1+\varepsilon)\sqrt{2\ln k/D}$ (Theorem 2.6), and from there on stable algorithms and Glauber dynamics provably fail. Theorem 2.7 shows that DQI with the USD decoder samples throughout $\beta<\beta_{\mathrm{ALG}}$, deep inside that shattered phase.
--
--   Differences from the source:
--   - reading: can efficiently solve (decoding); DQI can efficiently solve (sampling) → a deterministic multi-stack Turing machine writes, in C(N+1)^K steps, a circuit over the finite gate set {H, T, CNOT} with at most C(N+1)^K gates and wires; reason: the paper names no machine model or gate set; a finite gate set is the strong reading
--   - reading: fixed real parameters γ and β → the machine reads the instance and the binary digits of ⌊2^N γ⌋ (decoders of (A)), resp. ⌊2^N β⌋ (the decoders and the samplers of (B)); reason: γ and β are arbitrary reals; a machine cannot realize the rotations of an uncomputable parameter it does not read; restricting to computable β would be a special case; in (B) the decoders read the same digits as the sampler, so the sampler's machine can write the decoder circuits it runs
--   - encoding: with high probability (1 − o_N(1)); for sufficiently large N; 1 − √δ/ε − o_N(1) → ∃ machine, C, K and one sequence o → 0, chosen after k, D, δ and the clause's parameters and before N, such that the bound holds for every N ≥ k; reason: o absorbs finitely many small N; o does not depend on the instance
--   - reading: the quantum USD decoder of [CT23] can efficiently solve the (B, γ, δ)-problem → there exists an efficient decoder family solving it with probability 1 − o_N(1) over B; reason: the paper does not give the USD decoder's circuit; its exact behaviour is the milestones usd_decoder and coupling_markov
--   - reading: DQI can efficiently solve the (H_{B,J}, β, ε)-Gibbs sampling problem → (B1) the exact DQI law ν^{DQI} built from such a decoder family is within ε w.p. ≥ 1 − √δ/ε − o_N(1), for every fixed z₀, and (B2) an efficient sampler family over {H, T, CNOT} whose output law is within η_N → 0 of that ν^{DQI} (z₀ = all +1) on every instance, and within ε of µ w.p. ≥ 1 − √δ/ε − o_N(1); reason: compiling DQI to a finite gate set is approximate, so the efficient sampler is the compiled DQI up to a vanishing TV error, and the exact DQI law carries the bound of Theorem 2.4
--   - reading: decoder unitary → unitary of the decoder circuit on estimate wires [0, M), received wires [M, 2M) and work wires started in |0⟩; used in DQI through compute–copy–uncompute; reason: as in theorem_3_1
--   - reading: β < β_ALG(k, D) → 0 ≤ β; reason: β = sech⁻¹(1 − 2γ) ≥ 0 in (2.6), (3.10); a very negative β is the low-temperature regime of −J, which the proof does not reach
--   - encoding: β < tanh⁻¹(K_*(k)/D); K_*(k) := sup{d > 0 : max_{[0,1]} Φ_{d,k} = 1 − d/k} → tanh β < K_*(k)/D; sSup of {d > 0 : Φ_{d,k} ≤ 1 − d/k on [0, 1]}; reason: tanh is strictly increasing and K_*(k)/D < 1; Φ_{d,k}(0) = 1 − d/k
--   - reading: with Theorem 2.4 (the decoding clause at the matching error rate) → γ = 1/2 − 1/(2 cosh β) in (B1); reason: (2.6), (3.10)
--   - encoding: (B, J) ∼ 𝔾_ER(N, k, D); probability over (B, J) → uniform average over hyperedge lists and sign vectors v, J = (−1)^v; reason: Definition 2.5 is a finite uniform law; same instances
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 2.7, p.7; proof §3.2, pp.14–17

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_DQIShattered_DQI
import Definitions.Def_DQIShattered_Efficient

namespace DQIShattered

open Filter Topology

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, Theorem 2.7 (Gibbs sampling by DQI+USD), p.7.

Fix `k ≥ 3`, `D ≥ k` and `δ ∈ (0, 1)`; let `(B, J) ∼ 𝔾_ER(N, k, D)`.

**(A) Decoding.** For every `γ ∈ [0, γ_USD(k, D))` there is a polynomial-time decoder family solving the
`(B, γ, δ)`-quantum decoding problem with probability `1 − o_N(1)` over `B`.

**(B) Sampling.** For every `ε > 0` and every `β ≥ 0` with `β < β_ALG(k, D) = tanh⁻¹(K_*(k)/D)`, and
`γ = 1/2 − (1/2) sech β`:

1. *(DQI)* there is a decoder family as in (A) at this `γ` (its machine reading the digits of `β`) such that the exact DQI output law `ν^{DQI}_{B,J,β}`
   built from its decoder unitaries is within total variation `ε` of `µ_{β,H_{B,J}}` with probability at least
   `1 − √δ/ε − o_N(1)` over `(B, J)`, for every fixed `z₀`;
2. *(efficiently, by DQI)* there is a polynomial-time sampler family over `{H, T, CNOT}` that implements this DQI
   sampler: on every instance its output law is within total variation `η_N → 0` of `ν^{DQI}_{B,J,β}` (built from
   the same decoder circuits, with `z₀ = (+1, …, +1)`), and it is within total variation `ε` of `µ_{β,H_{B,J}}` with
   probability at least `1 − √δ/ε − o_N(1)` over `(B, J)`.

**Formalization Note** "Efficiently" is a Turing machine writing a circuit over `{H, T, CNOT}` of polynomial size in
polynomial time (`EfficientDecoders`, `EfficientSamplers`), on input the instance and the first `N` binary places
of the real parameter (`γ` in (A); `β` in (B), for the decoders as well as the sampler, so that the sampler's machine
can write the decoder circuits it runs). Every existential (machine, constants, `o`) comes after `k, D, δ` and the clause's own
parameters, and before `N`; `o_N(1)` absorbs "sufficiently large `N`". `β < tanh⁻¹(K_*(k)/D)` with `β ≥ 0` is
`tanh β < K_*(k)/D`. -/
theorem theorem_2_7 (k : ℕ) (hk : 3 ≤ k) (D : ℝ) (hD : (k : ℝ) ≤ D) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    (∀ γ : ℝ, 0 ≤ γ → γ < gammaUSD k D → ∃ circ, EfficientDecoders k D γ δ (fun N => encReal N γ) circ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 ≤ β → Real.tanh β < Kstar k / D →
      ∃ circ, EfficientDecoders k D (gammaOf β) δ (fun N => encReal N β) circ ∧
        (∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∀ N : ℕ, k ≤ N → ∀ x₀ : Fin N → ZMod 2,
          1 - Real.sqrt δ / ε - o N ≤ erProb N k D fun B v =>
            IsingLTL.BeliefProp.tvDist
              (nuDQI B v β (decoderMatrix (Mrows N k D) (circ N B))
                (zeroWork ((circ N B).wires - 2 * Mrows N k D)) x₀) (gibbs B v β) ≤ ε) ∧
        ∃ circ', EfficientSamplers k D β circ' ∧
          (∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ N : ℕ, k ≤ N →
            ∀ E : Fin (Mrows N k D) → KSet N k, ∀ v : Fin (Mrows N k D) → ZMod 2,
              IsingLTL.BeliefProp.tvDist (samplerDist N (circ' N (incidence E) v))
                (nuDQI (incidence E) v β (decoderMatrix (Mrows N k D) (circ N (incidence E)))
                  (zeroWork ((circ N (incidence E)).wires - 2 * Mrows N k D)) 0) ≤ η N) ∧
          ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∀ N : ℕ, k ≤ N →
            1 - Real.sqrt δ / ε - o N ≤ erProb N k D fun B v =>
              IsingLTL.BeliefProp.tvDist (samplerDist N (circ' N B v)) (gibbs B v β) ≤ ε := by sorry

end DQIShattered
