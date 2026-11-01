-- Prove2me | Theorems.Thm_BlockchainTFM_observation_1
-- name    : BlockchainTFM.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:47.521782+00:00
-- url     : https://prove2.me/theorems/da94cd73-4233-4056-9715-7abf63c7ea64
-- title:
--   Observation 1: $\tilde M$ is U-BNIC if $\mathbb E[\theta_i]=0$
-- statement:
--   Let valuations be i.i.d. from a law $V_0$ on $[0,1]$. Let $\tilde M=(\mathbf a,\tilde{\mathbf p},\tilde r)$ and $M=(\mathbf a,\mathbf p,r)$ be two transaction fee mechanisms with the same allocation rule, and let
--   $$\theta_i(b_i,\mathbf b_{-i})=a_i(b_i,\mathbf b_{-i})\bigl(\tilde p_i(b_i,\mathbf b_{-i})-p_i(b_i,\mathbf b_{-i})\bigr)\qquad(8)$$
--   be their payment difference. Suppose $M$ is U-BNIC. Then $\tilde M$ is U-BNIC if, for every user $i$ and every bid $b_i\in[0,1]$,
--   $$\mathbb E_{\mathbf b_{-i}\sim V_{-i}}\bigl[\theta_i(b_i,\mathbf b_{-i})\bigr]=0.\qquad(\text{EC.34})$$
--
--   User $i$'s utility under $\tilde M$ is her utility under $M$ minus $\theta_i$, so (EC.34) makes the two mechanisms give her the same expected utility at every bid. In the paper $M$ is the dominant auxiliary mechanism of $\tilde M$; the observation is the U-BNIC half of Theorem 2.
--
--   **Formalization Note** $\theta_i(b_i,\cdot)$ is assumed integrable for each $b_i\in[0,1]$, so that the expectation in (EC.34) exists.
--
--   Differences from the source:
--   - reading: Observation 1 states no hypothesis on M; its proof ends 'As mechanism M is U-BNIC' → hypothesis IsUBNIC V₀ M; reason: the hypothesis is the proof's last line; without it the observation is false
--   - generalization: M is the dominant auxiliary mechanism (a, p, 0) of M̃ → any TFM M with the same allocation rule as M̃ that is U-BNIC; reason: the proof uses only θ = a(p̃ − p) and U-BNIC of M; the dominant auxiliary is an instance
--   - generalization: V₀ has a pdf ρ on [0,1] → any probability measure V₀ on ℝ with V₀([0,1]) = 1; reason: the proof uses no density; every law with a pdf on [0,1] is an instance
--   - encoding: E[θ_i(b_i, b_{−i})] = 0 → θ_i(b_i,·) integrable against V₀^{⊗n} and its integral 0, for every i and b_i ∈ [0,1]; reason: integrability only excludes the case where the expectation is undefined
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Appendix EC.4.1, Observation 1 (EC.34)–(EC.35), p.ec10

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Properties

open MeasureTheory

namespace BlockchainTFM

/-- **Observation 1**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, p.ec10. Let
`M̃ = (a, p̃, r̃)` and its auxiliary mechanism `M = (a, p, 0)` share the allocation rule, let
`θ_i = a_i (p̃_i − p_i)` be their payment difference (8), and let `M` be U-BNIC. Then `M̃` is
U-BNIC if `E_{b_{-i}∼V_{-i}}[θ_i(b_i, b_{-i})] = 0` (EC.34) for every user `i` and bid `b_i`.

**Formalization Note.** The hypothesis "`M` is U-BNIC" is the last line of the paper's proof
("As mechanism `M` is U-BNIC, it holds that `M̃` is also U-BNIC"). `θ` is pinned to (8) by `hθ`.
(EC.34) is required for every bid `b_i ∈ [0,1]`, with `θ_i(b_i, ·)` integrable so that the
expectation exists. Only the allocation and payment rules of `M` and `M̃` matter (U-BNIC ignores
the miner revenue). `V₀` is a probability law carried by `[0,1]`. -/
theorem observation_1 {n : ℕ} (V₀ : Measure ℝ) [IsProbabilityMeasure V₀]
    (hV₀ : V₀ (Set.Icc 0 1) = 1) (M Mt : TFM n) (θ : (Fin n → ℝ) → Fin n → ℝ)
    (halloc : Mt.alloc = M.alloc)
    (hθ : ∀ b i, θ b i = M.alloc b i * (Mt.pay b i - M.pay b i))
    (hM : IsUBNIC V₀ M)
    (hθint : ∀ i : Fin n, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun b => θ (Function.update b i x) i) (Measure.pi fun _ : Fin n => V₀))
    (hθzero : ∀ i : Fin n, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∫ b, θ (Function.update b i x) i ∂(Measure.pi fun _ : Fin n => V₀) = 0) :
    IsUBNIC V₀ Mt := by sorry

end BlockchainTFM
