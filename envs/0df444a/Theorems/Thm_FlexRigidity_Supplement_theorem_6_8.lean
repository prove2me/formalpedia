-- Prove2me | Theorems.Thm_FlexRigidity_Supplement_theorem_6_8
-- name    : FlexRigidity.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:16:31.567235+00:00
-- url     : https://prove2.me/theorems/e4c2f6e6-79d0-4f39-98ff-d85c967cda99
-- title:
--   Theorem 6.8 — one-bit decision security with abort from search security
-- statement:
--   **Part 1, (78).** Let $\gamma\in(0,1)$, $\varepsilon_{\mathrm{tol}}\in(0,\tfrac{1-\gamma}2]$, $n$ a block length and $\mathrm{syn}$ a syndrome function, and suppose this instance of Protocol 3 is $\delta_{\mathrm{UE}}$-search secure. Then every attack against Protocol 4 built on it (device implementation, initial state, challenge choice, splitting and decoding) satisfies, with $p_{\mathrm{Acc}}=\Pr_{P'}[\mathrm{Acc}]$,
--   $$\Pr_{P'}[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{dec}}]-\frac{p_{\mathrm{Acc}}}{2}\le\frac12\,p_{\mathrm{Acc}}^{3/4}\,\delta_{\mathrm{UE}}^{1/4}\le\frac12\,\delta_{\mathrm{UE}}^{1/4}.$$
--
--   **Part 2.** Fix $\delta_{\mathrm{hon}}\in[0,\tfrac1{2\sqrt2}]$. For every $\gamma\in(0,1)$ there are $\vartheta_0\in(0,\tfrac12]$ and $\varepsilon_{\mathrm{tol}}(\vartheta)\to0$ as $\vartheta\to\vartheta_0^-$ such that for every $\vartheta\in(0,\vartheta_0)$, $\varepsilon_{\mathrm{tol}}(\vartheta)\in(0,\tfrac{1-\gamma}2]$ and for every $n\ge4/(1-\gamma)$, every syndrome function of length $\lfloor2m\,h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})\rfloor$ and every attack against Protocol 4,
--   $$\Pr_{P'}[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{dec}}]-\frac{p_{\mathrm{Acc}}}{2}\le\frac12\big(2^{2h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})}\omega^*\big)^{\vartheta m/4},\qquad m=\lfloor(1-\gamma)n/2\rfloor .$$
--
--   The baseline $p_{\mathrm{Acc}}/2$ is attained by decoders that always output the same fixed bit; the theorem turns the search security of Theorem 6.6 into one-bit uncloneable-indistinguishable security with abort.
--
--   **Formalization Note** $\omega^*$ is `quantumValue chshGame`; powers with real exponents are `Real.rpow` of nonnegative bases.
--
--   Differences from the source:
--   - reading: the underlying search protocol (Protocol 4's parameter: a search-secure instance of Protocol 3) → Part 1 for every γ ∈ (0,1), εtol ∈ (0,(1−γ)/2], n and syndrome function, with δUE-search security of that same instance assumed; reason: these are Protocol 2's parameter ranges, which Protocols 3 and 4 inherit
--   - encoding: Bob supplies two distinct one-bit plaintexts after preparation, keeping the post-measurement state → an instrument {J_{d0}} on Bob's register with outcome d0, challenges (d0, 1 − d0); d_b = d0 ⊕ b; reason: for one-bit plaintexts the pair is {0,1} (p. 61), so the only choice is its order
--   - encoding: with choice of γ, ϑ, εtol and the honest deficit δhon in Theorem 6.6 → δhon ∈ [0, 1/(2√2)] fixed first, then ∀ γ ∃ ϑ0 ∈ (0,½] ∃ εtol(·) with εtol → 0 at ϑ0⁻, ∀ ϑ ∈ (0,ϑ0), as in Theorem 6.6; reason: these are the existential choices of Theorems 5.6 and 6.6; µ does not occur in the conclusion
--   - encoding: the decision-security bound is at most ½(2^{2hbin(√2δhon)}ω*)^{ϑm/4} → Pr[Acc ∧ Bad_dec] − pAcc/2 ≤ ½(2^{2hbin(√2δhon)}ω*)^{ϑm/4} for every attack; reason: the decision-security bound is the εsec of Definition 6.2, Pr_DI[Acc ∧ Bad_dec] ≤ ½Pr_DI[Acc] + εsec
--   - generalization: Part 2 under Theorem 6.6's conditions (γδhon < εtol, syndrome of Fact 6.3) → Part 2 for every δhon ∈ [0, 1/(2√2)] and every syndrome function of the stated length; reason: the bound uses only Theorem 6.6's soundness, which needs neither; the source's case is an instance
--   - encoding: Protocol 3's key k and the decoders' access to public data → k = x_E of Protocol 2's run; splitting channel indexed by (d0, c_msg, σ, e), decoders' POVMs by (k, r, z) and the public data; reason: as in Theorem 6.6 (same joint law, copyable public data)
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Theorem 6.8, eq. (78), p. 65

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_CHSH
import Definitions.Def_FlexRigidity_Supplement_UE
import Definitions.Def_FlexRigidity_Supplement_Decision

set_option autoImplicit false

open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P35 (Density)

noncomputable section

namespace FlexRigidity.Supplement

/-- **Theorem 6.8 (Decision security with abort)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 65). Suppose the underlying search protocol is
`δ_UE`-search secure. For every attack against Protocol 4, with `p_Acc = Pr_{P′}[Acc]`,
`Pr_{P′}[Acc ∧ Bad_dec] − p_Acc/2 ≤ ½ p_Acc^{3/4} δ_UE^{1/4} ≤ ½ δ_UE^{1/4}` (78). For the choices
of `γ, ϑ`, the selected tolerance `ε_tol`, and the honest deficit `δ_hon` in Theorem 6.6, the
decision-security bound is at most `½ (2^{2h_bin(√2δ_hon)} ω*)^{ϑm/4}`.

**Formalization Note** Part 1: Protocol 4 is built on the same Protocol 3 instance (`n`, `γ`,
`ε_tol`, syndrome function `syn`) whose search security is assumed; the attack consists of the
device implementation, the initial state and Bob's post-acceptance operations (`DecisionAttack`).
Part 2: parameters as in Theorem 6.6 (`δ_hon` first, then `∀ γ ∃ ϑ₀ ∃ ε_tol(·)`), every syndrome
function of length `⌊2m h_bin(√2δ_hon)⌋`; the bound is on `Pr[Acc ∧ Bad_dec] − p_Acc/2`. -/
theorem theorem_6_8 :
    (∀ γ εtol : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 → εtol ∈ Set.Ioc 0 ((1 - γ) / 2) →
      ∀ (n s : ℕ) (syn : (Fin (mLen γ n) → Bool) → Fin s → Bool) (δUE : ℝ),
      IsSearchSecure γ εtol n syn δUE →
      ∀ I : DIImpl Bool Bool Bool Bool, I.IsAllowed n →
      ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
          (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
      ∀ att : DecisionAttack (mLen γ n) s (ueBobDim n r I), att.IsValid →
        decSucc (ueBlock γ εtol n I ρ0) syn att - accProb (ueBlock γ εtol n I ρ0) / 2 ≤
            1 / 2 * accProb (ueBlock γ εtol n I ρ0) ^ ((3 : ℝ) / 4) * δUE ^ ((1 : ℝ) / 4) ∧
          1 / 2 * accProb (ueBlock γ εtol n I ρ0) ^ ((3 : ℝ) / 4) * δUE ^ ((1 : ℝ) / 4) ≤
            1 / 2 * δUE ^ ((1 : ℝ) / 4)) ∧
    ∀ δ : ℝ, 0 ≤ δ ∧ δ ≤ 1 / (2 * Real.sqrt 2) →
    ∀ γ ∈ Set.Ioo (0 : ℝ) 1, ∃ ϑ0 ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ εf : ℝ → ℝ,
      Tendsto εf (𝓝[<] ϑ0) (𝓝 0) ∧
      ∀ ϑ ∈ Set.Ioo 0 ϑ0, εf ϑ ∈ Set.Ioc 0 ((1 - γ) / 2) ∧
        ∀ n : ℕ, 4 / (1 - γ) ≤ (n : ℝ) →
        ∀ syn : (Fin (mLen γ n) → Bool) → Fin (synLen (Real.sqrt 2 * δ) (mLen γ n)) → Bool,
        ∀ I : DIImpl Bool Bool Bool Bool, I.IsAllowed n →
        ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
            (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
        ∀ att : DecisionAttack (mLen γ n) (synLen (Real.sqrt 2 * δ) (mLen γ n)) (ueBobDim n r I),
          att.IsValid →
          decSucc (ueBlock γ (εf ϑ) n I ρ0) syn att - accProb (ueBlock γ (εf ϑ) n I ρ0) / 2 ≤
            1 / 2 * ((2 : ℝ) ^ (2 * hbin (Real.sqrt 2 * δ)) * quantumValue chshGame) ^
              (ϑ * (mLen γ n : ℝ) / 4) := by sorry

end FlexRigidity.Supplement
