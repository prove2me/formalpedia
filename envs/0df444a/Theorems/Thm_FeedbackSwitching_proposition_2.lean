-- Prove2me | Theorems.Thm_FeedbackSwitching_proposition_2
-- name    : FeedbackSwitching.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:14.334009+00:00
-- url     : https://prove2.me/theorems/4960b858-6893-4cb0-8c28-078dcc6977db
-- title:
--   Proposition 2 — self-financing exponential weights
-- statement:
--   Consider blocks $b=1,\dots,B$ of lengths $h_b$ summing to $T$, let $L_b$ be the sum of the loss vectors (in $[0,1]^K$) of block $b$, let $\pi_b$ be exponential weights with learning rate $\eta>0$ on vectors $\hat G_b\in\mathbb R^K$ from $\pi_1=\mathbf 1/K$, and $w_b=(1-\varepsilon)\pi_b+\varepsilon\mathbf 1/K$ with $0<\varepsilon\le1/2$. Let $\mathcal F_b$ be the history before block $b$, and let the block cost $C_b$ be the loss incurred in block $b$ plus the switches between consecutive rounds of block $b$ plus one. Suppose that for every block, almost surely,
--   $$
--   \mathbb E[\hat G_b\mid\mathcal F_b]=C_{w_b}L_b-\xi_b,\qquad\eta\|\hat G_b\|_\infty\le1,\qquad\mathbb E[C_b\mid\mathcal F_b]\le\langle w_b,L_b\rangle+\sigma_b-2\eta\,\mathbb E\big[\|\hat G_b\|_{w_b}^2\,\big|\,\mathcal F_b\big],
--   $$
--   where $\xi_b$ and $\sigma_b$ are $\mathcal F_b$-measurable. Then
--   $$
--   \mathrm{Reg}_T\le\frac{\log K}{\eta}+\sum_{b=1}^{B}\mathbb E\big[\sigma_b+2\|\xi_b\|_\infty\big]+\varepsilon T .
--   $$
--   The proposition moves the whole difficulty into a per-block condition: each block must pay for the second moment of its own estimate.
--
--   **Formalization Note** Blocks and rounds are 0-based; $(\mathcal F_b)$ is a nondecreasing family of sub-σ-algebras, the actions of block $b$ and $\hat G_b$ are $\mathcal F_{b+1}$-measurable; $\pi_b$ is `wmWeights`. Conditional expectations are coordinatewise.
--
--   Differences from the source:
--   - reading: F_b is the history before block b; the learner runs a randomized procedure that may depend on the past → a nondecreasing family of sub-σ-algebras F_b; the actions of block b and Ĝ_b are F_{b+1}-measurable; ξ_b, σ_b are F_b-measurable; reason: this is what "history before block b" means for the random objects of the proposition; the proof uses that π_b, w_b, ξ_b are fixed given F_b
--   - encoding: E[σ_b + 2‖ξ_b‖_∞] → σ_b and ‖ξ_b‖_∞ assumed integrable; reason: σ_b is bounded below by the block condition and ξ_b is bounded, so a non-integrable σ_b means E σ_b = +∞ and the paper's bound is trivially true; the assumption excludes only that case and Lean's junk integral 0
--   - encoding: K actions (K ≥ 1 implicit) → NeZero K; reason: the regret's minimum over i ∈ [K] and the uniform start 1/K need K ≥ 1; nondegeneracy only
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Proposition 2, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_FeedbackSwitching_centering
import Definitions.Def_FeedbackSwitching_regret
open MeasureTheory Matrix
open scoped Classical

namespace FeedbackSwitching

/-- **Proposition 2 (Self-financing exponential weights)**, p.24 (PDF p.26). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

Blocks `b = 1, …, B` of lengths `h_b` summing to `T`; `L_b` is the sum of the loss vectors of block
`b`; `π_b` is exponential weights with learning rate `η` on the vectors `Ĝ_b` (as in Lemma 2, from
`π_1 = 1/K`), `w_b = (1 − ε)π_b + ε1/K` with `0 < ε ≤ 1/2`; `F_b` is the history before block
`b`; the block cost `C_b` is the loss incurred in block `b`, plus the switches between consecutive
rounds of block `b`, plus one. If for every block, almost surely,
`E[Ĝ_b | F_b] = C_{w_b} L_b − ξ_b`, `η‖Ĝ_b‖_∞ ≤ 1`,
`E[C_b | F_b] ≤ ⟨w_b, L_b⟩ + σ_b − 2η E[‖Ĝ_b‖²_{w_b} | F_b]`, with `ξ_b`, `σ_b` `F_b`-measurable,
then `Reg_T ≤ log K/η + ∑_b E[σ_b + 2‖ξ_b‖_∞] + εT`.

**Formalization Note.** Rounds and blocks are 0-based; block `b` is the rounds
`[s_b, s_b + h_b)`, `s_b = ∑_{c<b} h_c`. `(F_b)` is a nondecreasing family of sub-σ-algebras; the
actions of block `b` and `Ĝ_b` are `F_{b+1}`-measurable (they are known once block `b` is over),
so `π_b` and `w_b` are `F_b`-measurable. `π_b = wmWeights η Ĝ b` (exponential weights, uniform at
`b = 0`). Conditional expectations are taken coordinatewise. `‖ξ‖_∞` is the sup norm of
`Fin K → ℝ`. `σ_b` and `ξ_b` are assumed integrable, so that `E[σ_b + 2‖ξ_b‖_∞]` is a true
expectation. Losses are deterministic (oblivious adversary) in `[0,1]^K`. -/
theorem proposition_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} [NeZero K] (T B : ℕ) (hb : ℕ → ℕ) (hsum : ∑ b ∈ Finset.range B, hb b = T)
    (η ε : ℝ) (hη : 0 < η) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t < T, InUnitCube (ℓ t))
    (F : ℕ → MeasurableSpace Ω) (hF_le : ∀ b, F b ≤ mΩ) (hF_mono : Monotone F)
    (I : ℕ → Ω → Fin K) (Ghat : ℕ → Ω → Fin K → ℝ) (ξ : ℕ → Ω → Fin K → ℝ) (σ : ℕ → Ω → ℝ)
    (hI_meas : ∀ b < B, ∀ t ∈ Finset.Ico (∑ c ∈ Finset.range b, hb c)
      (∑ c ∈ Finset.range b, hb c + hb b), Measurable[F (b + 1)] (I t))
    (hG_meas : ∀ b, Measurable[F (b + 1)] (Ghat b))
    (hξ_meas : ∀ b, Measurable[F b] (ξ b)) (hσ_meas : ∀ b, Measurable[F b] (σ b))
    (hξ_int : ∀ b < B, Integrable (fun ω => ‖ξ b ω‖) μ) (hσ_int : ∀ b < B, Integrable (σ b) μ)
    (hmean : ∀ b < B, ∀ i,
      μ[fun ω => Ghat b ω i | F b] =ᵐ[μ] fun ω =>
        (centering (fun j => (1 - ε) * UnderstandingML.wmWeights η (fun c => Ghat c ω) b j + ε / K) *ᵥ
          (∑ t ∈ Finset.Ico (∑ c ∈ Finset.range b, hb c) (∑ c ∈ Finset.range b, hb c + hb b), ℓ t)) i
          - ξ b ω i)
    (hbound : ∀ b < B, ∀ᵐ ω ∂μ, ∀ i, η * |Ghat b ω i| ≤ 1)
    (hcost : ∀ b < B,
      μ[fun ω => ∑ t ∈ Finset.Ico (∑ c ∈ Finset.range b, hb c) (∑ c ∈ Finset.range b, hb c + hb b),
            ℓ t (I t ω) +
          ∑ t ∈ Finset.Ico (∑ c ∈ Finset.range b, hb c) (∑ c ∈ Finset.range b, hb c + hb b - 1),
            (if I (t + 1) ω ≠ I t ω then (1 : ℝ) else 0) + 1 | F b]
        ≤ᵐ[μ] fun ω =>
          (fun j => (1 - ε) * UnderstandingML.wmWeights η (fun c => Ghat c ω) b j + ε / K) ⬝ᵥ
              (∑ t ∈ Finset.Ico (∑ c ∈ Finset.range b, hb c) (∑ c ∈ Finset.range b, hb c + hb b), ℓ t)
            + σ b ω
            - 2 * η * μ[fun ω' => wNormSq
                (fun j => (1 - ε) * UnderstandingML.wmWeights η (fun c => Ghat c ω') b j + ε / K)
                (Ghat b ω') | F b] ω) :
    (∫ ω, (∑ t ∈ Finset.range T, ℓ t (I t ω) + pathSwitches T (fun t => I t ω)) ∂μ)
        - ⨅ i : Fin K, ∑ t ∈ Finset.range T, ℓ t i
      ≤ Real.log K / η + ∑ b ∈ Finset.range B, ∫ ω, (σ b ω + 2 * ‖ξ b ω‖) ∂μ + ε * T := by sorry

end FeedbackSwitching
