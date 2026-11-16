-- Prove2me | Theorems.Thm_FlexRigidity_Supplement_theorem_6_10
-- name    : FlexRigidity.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:18:09.674205+00:00
-- url     : https://prove2.me/theorems/08ee7b81-4690-4799-a748-c8983b67fe26
-- title:
--   Theorem 6.10 — copy-protection security of multi-bit point functions
-- statement:
--   **Part 1, (79).** Let $\gamma\in(0,1)$, $\varepsilon_{\mathrm{tol}}\in(0,\tfrac{1-\gamma}2]$, $n$ with $m=\lfloor(1-\gamma)n/2\rfloor\ge1$, a syndrome function and a hash length $\tau$, and suppose this instance of Protocol 3 is $\delta_{\mathrm{UE}}$-search secure. Then in the experiment of Definition 6.3 every attack against Protocol 5 satisfies
--   $$\Pr[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{copy}}]\le\frac{p_{\mathrm{Acc}}}{2}+2^{\tau-1}\delta_{\mathrm{UE}},\qquad p_{\mathrm{Acc}}=\Pr[\mathrm{Acc}].$$
--
--   **Part 2.** Fix $\delta_{\mathrm{hon}}\in[0,\tfrac1{2\sqrt2}]$ and write $q=2^{2h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})}\omega^*$. For every $\gamma\in(0,1)$ there are $\vartheta_0\in(0,\tfrac12]$ and $\varepsilon_{\mathrm{tol}}(\vartheta)\to0$ as $\vartheta\to\vartheta_0^-$ such that for every $\vartheta\in(0,\vartheta_0)$, $\varepsilon_{\mathrm{tol}}(\vartheta)\in(0,\tfrac{1-\gamma}2]$ and:
--
--   1. for every $n\ge4/(1-\gamma)$, every hash length $\tau$, every syndrome function of length $\lfloor2m\,h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})\rfloor$ and every attack, the piracy advantage is at most $2^{\tau-1}q^{\vartheta m}$;
--   2. if $2h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})<\log(1/\omega^*)$, then with
--   $$\tau(n)=\Big\lfloor\frac{\vartheta m}{2}\big[\log(1/\omega^*)-2h_{\mathrm{bin}}(\sqrt2\delta_{\mathrm{hon}})\big]\Big\rfloor$$
--   there are $c>0$ and $K$ such that for every $n\ge4/(1-\gamma)$ the hash-collision error $2^{-\tau(n)}$ and the piracy advantage of every attack are at most $K\,2^{-cn}$; and if moreover $\gamma\delta_{\mathrm{hon}}<\varepsilon_{\mathrm{tol}}$ and the syndrome is a scheme as specified in Fact 6.3 (constant $C$), there is a negligible function $f$ such that the honest pointwise failure of Protocol 5 at every fixed $(y,v,x)$ is at most $f(n)$, i.e. the honest pointwise success is $1-\mathrm{negl}(n)$.
--
--   This gives sequential device-independent copy protection of multi-bit point functions, with a short public hash in place of a quantum random oracle.
--
--   **Formalization Note** The piracy advantage is $\Pr[\mathrm{Acc}\wedge\mathrm{Bad}_{\mathrm{copy}}]-p_{\mathrm{Acc}}/2$; $\omega^*$ is `quantumValue chshGame`; negligibility is the published `PPADSIS.SubexpSIS.Negligible` (nonnegative and eventually below $n^{-c}$ for every $c>0$).
--
--   Differences from the source:
--   - encoding: every attack against Protocol 5 (any parameters) → Part 1 assumes m = ⌊(1−γ)n/2⌋ ≥ 1, γ ∈ (0,1), εtol ∈ (0,(1−γ)/2]; reason: for m = 0 the challenge set {0,1}^m \ {y} is empty and the experiment is undefined; the parameter ranges are Protocol 2's
--   - encoding: piracy advantage → copySucc − accProb/2, i.e. Pr[Acc ∧ Bad_copy] − Pr[Acc]/2; reason: Definition 6.3's baseline ½Pr[Acc]
--   - encoding: using the choices of γ, ϑ, εtol and µ from Theorem 5.6 in Protocol 3 → δhon ∈ [0, 1/(2√2)] fixed first, then ∀ γ ∃ ϑ0 ∈ (0,½] ∃ εtol(·) with εtol → 0 at ϑ0⁻, ∀ ϑ ∈ (0,ϑ0); µ not quantified; reason: as in Theorem 6.6; µ does not occur in the conclusion
--   - generalization: the explicit piracy bound for Theorem 6.6's setting → for every δhon ∈ [0, 1/(2√2)], every τ and every syndrome function of the stated length, without γδhon < εtol; reason: the bound uses only (79) and Theorem 6.6's soundness, which needs neither; the source's case is an instance
--   - reading: taking τ = (ϑm/2)[log(1/ω*) − 2hbin(√2δhon)] → τ(n) = ⌊(ϑm/2)(log₂(1/ω*) − 2hbin(√2δhon))⌋ under the hypothesis 2hbin(√2δhon) < log₂(1/ω*); reason: τ is a number of matrix rows; the hypothesis is what makes the printed τ a growing length (otherwise no exponential decay is possible), and the floor changes 2^{−τ} by at most a factor 2
--   - reading: exponentially small piracy advantage and hash-collision error for fixed γ, ϑ, δhon → ∃ c > 0 ∃ K, ∀ n ≥ 4/(1−γ), 2^{−τ(n)} ≤ K·2^{−cn} and every attack's piracy advantage ≤ K·2^{−cn}; reason: the standard meaning of "exponentially small in n" with constants depending on the fixed γ, ϑ, δhon
--   - reading: together with Lemma 6.9, honest pointwise success 1 − negl(n) → under γδhon < εtol and a Fact 6.3 scheme, ∃ negligible f with honest failure at every fixed (y, v, x) ≤ f(n), for all n; reason: Lemma 6.9's εcorr for the honest model of Theorem 6.6 needs exactly these conditions (p. 68); "uniformly over (y, v, x)" is how Lemma 6.9 is stated
--   - encoding: Protocol 5 with prescribed uniform key k = y; decoders given only their own challenge → y = x_E of Protocol 2's run; splitting channel indexed by (c_msg, σ, R, z); decoder j's POVM indexed by its own challenge and the public data; reason: same joint law (p. 63); public data can be copied to both decoders
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Theorem 6.10, eq. (79), p. 68

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_Syndrome
import Definitions.Def_FlexRigidity_Supplement_CHSH
import Definitions.Def_FlexRigidity_Supplement_UE
import Definitions.Def_FlexRigidity_Supplement_UEHonest
import Definitions.Def_FlexRigidity_Supplement_CopyProtection

set_option autoImplicit false

open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P35 (Density)

noncomputable section

namespace FlexRigidity.Supplement

/-- **Theorem 6.10 (Copy-protection security)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 68). Suppose Protocol 3 is `δ_UE`-search secure.
Then, in the experiment of Definition 6.3, every attack against Protocol 5 satisfies
`Pr[Acc ∧ Bad_copy] ≤ p_Acc/2 + 2^{τ−1} δ_UE`, `p_Acc = Pr[Acc]` (79). Using the choices of
`γ, ϑ, ε_tol, µ` from Theorem 5.6 in Protocol 3, the piracy advantage in Protocol 5 is at most
`2^{τ−1} (2^{2h_bin(√2δ_hon)} ω*)^{ϑm}`. Taking `τ = (ϑm/2)[log(1/ω*) − 2h_bin(√2δ_hon)]` gives
exponentially small piracy advantage and hash-collision error for fixed `γ, ϑ, δ_hon`; together
with Lemma 6.9 this gives honest pointwise success `1 − negl(n)`.

**Formalization Note** Part 1 is for every Protocol 3 instance with `m ≥ 1` (for `m = 0` the
challenge set `{0,1}^m \ {y}` is empty). The piracy advantage is `Pr[Acc ∧ Bad_copy] − p_Acc/2`.
Part 2 fixes `δ_hon` first, then `∀ γ ∃ ϑ₀ ∃ ε_tol(·)` as in Theorem 5.6, `n ≥ 4/(1−γ)`, every hash
length `τ` and every syndrome function of length `⌊2m h_bin(√2δ_hon)⌋`. The prescribed `τ` is the
floor of the printed expression, and requires `log₂(1/ω*) > 2h_bin(√2δ_hon)`. "Exponentially
small" is `≤ K·2^{−cn}` with `c > 0` for all `n ≥ 4/(1−γ)` (constants depending on `γ, ϑ, δ_hon`);
the hash-collision error is `2^{−τ}`. "Honest pointwise success `1 − negl(n)`" is: under
`γδ_hon < ε_tol` and a syndrome scheme of Fact 6.3, the honest failure probability at every fixed
`(y, v, x)` is bounded by one negligible function of `n`. -/
theorem theorem_6_10 :
    (∀ γ εtol : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 → εtol ∈ Set.Ioc 0 ((1 - γ) / 2) →
      ∀ (n s τ : ℕ), 1 ≤ mLen γ n →
      ∀ (syn : (Fin (mLen γ n) → Bool) → Fin s → Bool) (δUE : ℝ),
      IsSearchSecure γ εtol n syn δUE →
      ∀ I : DIImpl Bool Bool Bool Bool, I.IsAllowed n →
      ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
          (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
      ∀ att : CopyAttack (mLen γ n) s τ (ueBobDim n r I), att.IsValid →
        copySucc τ (ueBlock γ εtol n I ρ0) syn att ≤
          accProb (ueBlock γ εtol n I ρ0) / 2 + (2 : ℝ) ^ ((τ : ℝ) - 1) * δUE) ∧
    ∀ δ : ℝ, 0 ≤ δ ∧ δ ≤ 1 / (2 * Real.sqrt 2) →
    ∀ γ ∈ Set.Ioo (0 : ℝ) 1, ∃ ϑ0 ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ εf : ℝ → ℝ,
      Tendsto εf (𝓝[<] ϑ0) (𝓝 0) ∧
      ∀ ϑ ∈ Set.Ioo 0 ϑ0, εf ϑ ∈ Set.Ioc 0 ((1 - γ) / 2) ∧
        (∀ n : ℕ, 4 / (1 - γ) ≤ (n : ℝ) → ∀ τ : ℕ,
          ∀ syn : (Fin (mLen γ n) → Bool) → Fin (synLen (Real.sqrt 2 * δ) (mLen γ n)) → Bool,
          ∀ I : DIImpl Bool Bool Bool Bool, I.IsAllowed n →
          ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
              (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
          ∀ att : CopyAttack (mLen γ n) (synLen (Real.sqrt 2 * δ) (mLen γ n)) τ (ueBobDim n r I),
            att.IsValid →
            copySucc τ (ueBlock γ (εf ϑ) n I ρ0) syn att - accProb (ueBlock γ (εf ϑ) n I ρ0) / 2 ≤
              (2 : ℝ) ^ ((τ : ℝ) - 1) *
                ((2 : ℝ) ^ (2 * hbin (Real.sqrt 2 * δ)) * quantumValue chshGame) ^
                  (ϑ * (mLen γ n : ℝ))) ∧
        (2 * hbin (Real.sqrt 2 * δ) < Real.logb 2 (1 / quantumValue chshGame) →
          let τf : ℕ → ℕ := fun n => ⌊ϑ * (mLen γ n : ℝ) / 2 *
            (Real.logb 2 (1 / quantumValue chshGame) - 2 * hbin (Real.sqrt 2 * δ))⌋₊
          (∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ n : ℕ, 4 / (1 - γ) ≤ (n : ℝ) →
            (2 : ℝ) ^ (-(τf n : ℝ)) ≤ K * (2 : ℝ) ^ (-(c * n)) ∧
            ∀ syn : (Fin (mLen γ n) → Bool) → Fin (synLen (Real.sqrt 2 * δ) (mLen γ n)) → Bool,
            ∀ I : DIImpl Bool Bool Bool Bool, I.IsAllowed n →
            ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
                (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
            ∀ att : CopyAttack (mLen γ n) (synLen (Real.sqrt 2 * δ) (mLen γ n)) (τf n)
                (ueBobDim n r I), att.IsValid →
              copySucc (τf n) (ueBlock γ (εf ϑ) n I ρ0) syn att -
                  accProb (ueBlock γ (εf ϑ) n I ρ0) / 2 ≤ K * (2 : ℝ) ^ (-(c * n))) ∧
          (γ * δ < εf ϑ →
            ∀ (syn : (m : ℕ) → (Fin m → Bool) → Fin (synLen (Real.sqrt 2 * δ) m) → Bool)
              (dec : (m : ℕ) → (Fin (synLen (Real.sqrt 2 * δ) m) → Bool) → (Fin m → Bool) →
                (Fin m → Bool))
              (C : ℝ), IsSyndromeScheme (Real.sqrt 2 * δ) syn dec C →
              ∃ f : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible f ∧
                ∀ (n : ℕ) (y v x : Fin (mLen γ n) → Bool),
                  honestCopyFail δ γ (εf ϑ) n (τf n) (syn (mLen γ n)) (dec (mLen γ n)) y v x ≤
                    f n)) := by sorry

end FlexRigidity.Supplement
