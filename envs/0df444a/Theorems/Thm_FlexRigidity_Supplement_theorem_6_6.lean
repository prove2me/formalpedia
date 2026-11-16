-- Prove2me | Theorems.Thm_FlexRigidity_Supplement_theorem_6_6
-- name    : FlexRigidity.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:14:58.701196+00:00
-- url     : https://prove2.me/theorems/9bff80ad-1aa0-4a08-98a2-3ec0a286539a
-- title:
--   Theorem 6.6 — sequential DI uncloneable encryption under depolarizing noise (completeness and search security)
-- statement:
--   Fix the honest noise level $\delta_{\mathrm{hon}}\in[0,\tfrac1{2\sqrt2}]$ and write $\omega^*$ for the quantum value of CHSH and
--   $$q=2^{2h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})}\,\omega^* .$$
--   For every testing probability $\gamma\in(0,1)$ there are $\vartheta_0\in(0,\tfrac12]$ and a tolerance function $\varepsilon_{\mathrm{tol}}(\vartheta)$ with $\varepsilon_{\mathrm{tol}}(\vartheta)\to0$ as $\vartheta\to\vartheta_0^-$ such that for every $\vartheta\in(0,\vartheta_0)$, $\varepsilon_{\mathrm{tol}}(\vartheta)\in(0,\tfrac{1-\gamma}2]$, and for every $n\ge 4/(1-\gamma)$, with $m=\lfloor(1-\gamma)n/2\rfloor$, Protocol 3 satisfies:
--
--   1. **Completeness.** If $\gamma\delta_{\mathrm{hon}}<\varepsilon_{\mathrm{tol}}$ and the syndrome is a scheme as specified in Fact 6.3 for $\delta_{\mathrm{err}}=\sqrt2\delta_{\mathrm{hon}}$ with constant $C$, the honest implementation (depolarizing noise $2\sqrt2\delta_{\mathrm{hon}}$) satisfies
--   $$\Pr_{P'}[\mathrm{Acc}\wedge(\text{Honest Bob decrypts correctly})]\ge 1-6\exp\Big(-\frac{8n(\varepsilon_{\mathrm{tol}}-\gamma\delta_{\mathrm{hon}})^2}{9}\Big)-C\cdot2^{-m^{1/3}}.$$
--   2. **Search soundness.** For every syndrome function of length $\lfloor 2m\,h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})\rfloor$, Protocol 3 is $q^{\vartheta m}$-search secure: every allowed implementation and attack satisfies
--   $$\Pr_{P'}[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{search}}]\le\big(2^{2h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})}\omega^*\big)^{\vartheta m}.$$
--
--   This is the first device-independent application of the paper's DD-to-DI conversion (Theorem 5.6): the Wiesner-state uncloneable encryption scheme of Broadbent and Lord becomes a sequential DI scheme with exponentially small search-cloning probability whenever $q<1$.
--
--   **Formalization Note** The attack consists of every device implementation allowed by Postulate Set 5.4, every initial state, every splitting channel and every pair of decoders; $\omega^*$ is `quantumValue chshGame`. The exponent $\vartheta m$ is real.
--
--   Differences from the source:
--   - encoding: Alice samples the key k first and sets x_i = k_j on the j-th generation round (Protocol 3 step 2(a)) → in the soundness clause k = x_E of Protocol 2's run with x uniform; the completeness clause samples k first and prescribes x_i = k_j; reason: p. 63 notes the joint law of (U, X, Y) and of the device inputs is exactly Protocol 2's; the two descriptions give the same distribution
--   - encoding: with choice of γ, ϑ, εtol and µ from Theorem 5.6 → ∀ γ ∃ ϑ0 ∈ (0,½] ∃ εtol(·) with εtol(ϑ) → 0 as ϑ → ϑ0⁻, ∀ ϑ ∈ (0,ϑ0), εtol(ϑ) ∈ (0,(1−γ)/2]; µ not quantified; reason: µ enters only the proof (q_dep is constant in µ here, p. 64), so an existential µ with no constraint in the conclusion changes nothing
--   - reading: honest depolarizing noise 2√2δhon (no quantifier order stated) → δhon ∈ [0, 1/(2√2)] fixed before γ; ϑ0 and εtol may depend on δhon but not on n, the syndrome function or the attack; reason: q_dep = 2^{2hbin(√2δhon)}ω* depends on δhon and Theorem 5.6's choices depend on q_dep; 2√2δhon ≤ 1 is the range of a depolarizing weight
--   - generalization: soundness under the conditions of Theorem 5.5 and with the syndrome of Fact 6.3 → soundness for every δhon ∈ [0, 1/(2√2)] and every syndrome function of length ⌊2m hbin(√2δhon)⌋; reason: the soundness proof (p. 64) uses only the syndrome length; the source's case is an instance
--   - generalization: syndrome as specified in Fact 6.3 ([Arı10] scheme), error O(2^{−m^{1/3}}) → every scheme family whose decoding error on the honest distribution (A uniform, i.i.d. Bernoulli(√2δhon) noise) is ≤ C·2^{−m^{1/3}} for all m; the O(·) term is C·2^{−m^{1/3}}; reason: the completeness proof uses only this error bound on that distribution; the [Arı10] scheme is one such family with its constant C
--   - encoding: Bob's ciphertext is his quantum memory with the public classical data; decoders receive the key after the split → Bob's register = memory M^B_{n+1}, R and transcript (published finalOp); splitting channel indexed by (c_msg, syndrome); decoders' POVMs indexed by key and public data, finite dimensions; reason: classical public data can be copied to both decoders, so letting their measurements read it adds no power
--   - encoding: honest implementation with EPR pairs depolarized by 2√2δhon, Bob storing his halves and later measuring in the key's bases → explicit product law over rounds (UEHonest), Bob's decrypting outcome recorded in the generation record; reason: honest rounds are independent and identical (p. 60); the product is exactly the joint law of all honest classical outcomes
--   - encoding: ω* = 1/2 + 1/(2√2) → quantumValue chshGame; reason: same number (Tsirelson's bound); the value is a fact to prove, not a hypothesis
--   - encoding: Honest Bob decrypts the plaintext correctly → the corrected string dec(syn(a_E), b_E) equals a_E; reason: honest decryption outputs c_msg ⊕ dec(syn(a_E), b_E) with c_msg = msg ⊕ a_E, which equals msg exactly when dec(syn(a_E), b_E) = a_E, for every plaintext msg
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Theorem 6.6, p. 64

import Mathlib
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_Syndrome
import Definitions.Def_FlexRigidity_Supplement_CHSH
import Definitions.Def_FlexRigidity_Supplement_UE
import Definitions.Def_FlexRigidity_Supplement_UEHonest

set_option autoImplicit false

open Filter Topology

noncomputable section

namespace FlexRigidity.Supplement

/-- **Theorem 6.6 (Sequential DI UE security under depolarizing noise)** (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 64). Under Postulate Set 5.4,
with choice of `γ, ϑ, ε_tol` and `µ` from Theorem 5.6, honest depolarizing noise `2√2 δ_hon`
satisfying the conditions of Theorem 5.5, and syndrome as specified in Fact 6.3, Protocol 3
satisfies
`Pr_{P′}[Acc ∧ (Honest Bob decrypts correctly)] ≥ 1 − 6 exp(−8n(ε_tol − γδ_hon)²/9) − O(2^{−m^{1/3}})`
and `Pr_{P′}[Acc ∧ Bad_search] ≤ (2^{2h_bin(√2δ_hon)} ω*)^{ϑm}`.

**Formalization Note** The noise level `δ_hon ∈ [0, 1/(2√2)]` is fixed first (it fixes
`q_dep = 2^{2h_bin(√2δ_hon)} ω*`, p. 64); then, as in Theorem 5.6, `∀ γ ∃ ϑ₀ ∈ (0, ½] ∃ ε_tol(·)`
with `ε_tol(ϑ) → 0` as `ϑ → ϑ₀⁻`, for every `ϑ ∈ (0, ϑ₀)` and every `n ≥ 4/(1−γ)`;
`m = ⌊(1−γ)n/2⌋`. `µ` does not occur in the conclusion (q_dep is constant in `µ`) and is not
quantified. Completeness assumes `γδ_hon < ε_tol` (Theorem 5.5) and a syndrome scheme with
decoding error `≤ C·2^{−m^{1/3}}` (Fact 6.3), the `O(·)` being this `C`. Soundness is stated for
every syndrome function of length `s = ⌊2m h_bin(√2δ_hon)⌋` and every `δ_hon` in range, as
`δ`-search security (every allowed implementation, initial state, splitting and decoding). `ω*` is
`quantumValue chshGame`. -/
theorem theorem_6_6 (δ : ℝ) (hδ : 0 ≤ δ ∧ δ ≤ 1 / (2 * Real.sqrt 2)) :
    ∀ γ ∈ Set.Ioo (0 : ℝ) 1, ∃ ϑ0 ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ εf : ℝ → ℝ,
      Tendsto εf (𝓝[<] ϑ0) (𝓝 0) ∧
      ∀ ϑ ∈ Set.Ioo 0 ϑ0, εf ϑ ∈ Set.Ioc 0 ((1 - γ) / 2) ∧
        ∀ n : ℕ, 4 / (1 - γ) ≤ (n : ℝ) →
          (γ * δ < εf ϑ →
            ∀ (syn : (m : ℕ) → (Fin m → Bool) → Fin (synLen (Real.sqrt 2 * δ) m) → Bool)
              (dec : (m : ℕ) → (Fin (synLen (Real.sqrt 2 * δ) m) → Bool) → (Fin m → Bool) →
                (Fin m → Bool))
              (C : ℝ), IsSyndromeScheme (Real.sqrt 2 * δ) syn dec C →
              1 - 6 * Real.exp (-(8 * (n : ℝ) * (εf ϑ - γ * δ) ^ 2) / 9)
                  - C * (2 : ℝ) ^ (-((mLen γ n : ℝ) ^ ((1 : ℝ) / 3)))
                ≤ ueHonestSucc δ γ (εf ϑ) n (syn (mLen γ n)) (dec (mLen γ n))) ∧
          ∀ syn : (Fin (mLen γ n) → Bool) → Fin (synLen (Real.sqrt 2 * δ) (mLen γ n)) → Bool,
            IsSearchSecure γ (εf ϑ) n syn
              (((2 : ℝ) ^ (2 * hbin (Real.sqrt 2 * δ)) * quantumValue chshGame) ^
                (ϑ * (mLen γ n : ℝ))) := by sorry

end FlexRigidity.Supplement
