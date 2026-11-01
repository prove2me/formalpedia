-- Prove2me | Theorems.Thm_BlockchainTFM_theorem_4
-- name    : BlockchainTFM.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:53.653849+00:00
-- url     : https://prove2.me/theorems/6d5304cc-2ba3-421c-aa7a-4a4976e2059d
-- title:
--   Theorem 4 (Main Theorem): Mechanism 3 is U-BNIC and 1-SCP; UIR and BF for $n\ge\max\{\lambda_0k,30\}$; $(C,O(\frac1{1-C}))$-U-SP (corrected: $c_\rho=\mathbb E[v^2]$)
-- statement:
--   Let valuations be i.i.d. from a law $V_0$ on $[0,1]$ with $c_\rho=\mathbb E_{v\sim V_0}[v^2]>0$, and let $\tilde M=(\mathbf a,\tilde{\mathbf p},\tilde r)$ be Mechanism 3 with block size $k$, logit parameter $m$ and scaling parameter $h$.
--
--   1. **(A) Incentives and collusion.** For any block size $k\ge1$, any $n\ge2$ and any parameters $m,h\in[0,+\infty)$, Mechanism 3 is U-BNIC and 1-SCP.
--   2. **(B) Rationality and feasibility.** For any fixed $\lambda_0>\frac{e}{e-1}\approx1.582$, any $k\ge1$ and any $n\ge\max\{\lambda_0k,30\}$, set
--   $$m=m_\#(\lambda_0)=\min\Bigl\{\tfrac12\ln\frac{1}{\ln\frac{\lambda_0}{\lambda_0-1}},\,1\Bigr\}.$$
--   Then for every
--   $$h\in\Bigl[0,\ g(\lambda_0)\frac{2kc_\rho(n-1)}{en^2}\Bigr],\qquad g(\lambda_0)=\frac{m\cdot\max\bigl\{1-\sqrt{\ln\frac{\lambda_0}{\lambda_0-1}},\ 1-e\ln\frac{\lambda_0}{\lambda_0-1}\bigr\}}{e^{\,m-1+\frac{e}{0.9\lambda_0-1}}},$$
--   Mechanism 3 is UIR and BF.
--   3. **(C) Sybil-proofness.** The mechanism is $\bigl(C,O(\frac1{1-C})\bigr)$-U-SP for every $C\in[0,1)$: there is an absolute constant $K$ such that, for every $\lambda_0>e/(e-1)$, $k\ge1$ and $V_0$ as above, and every choice of $h_\eta\in[0,g(\lambda_0)\frac{2kc_\rho(\eta-1)}{e\eta^2}]$ for each bid count $\eta\ge\max\{\lambda_0k,30\}$, the variable-bid-size mechanism that runs Mechanism 3 with $m_\#(\lambda_0)$ and $h_\eta$ on $\eta$ bids is $(C,K/(1-C))$-U-SP for every $C\in[0,1)$, on numbers of real users $n\ge\max\{\lambda_0k,30\}$.
--
--   Together with $\mathbb E[\tilde r(\mathbf b)]=\frac14hnc_\rho$, the theorem gives a transaction fee mechanism for general block size that is Bayesian incentive compatible, side-contract-proof against the miner and one user, individually rational, budget feasible and Sybil-proof, while paying the miner a constant fraction of the optimal revenue once $n\ge\max\{\lambda_0k,30\}$.
--
--   **Formalization Note** U-BNIC and U-SP include the existence (integrability) of the expectations involved. $n\ge2$ and $c_\rho>0$ make the mechanism's division by $c_\rho(n-1)$ meaningful.
--
--   Differences from the source:
--   - correction: c_ρ = ∫₀¹ ρ²(t) dt (18) → c_ρ = ∫ t² dV₀(t) = E[v²] (crho); reason: with ∫ρ², (11) fails: n = 2, V₀ uniform gives ∫ρ² = 1 and E_{b₂}[θ₁(b₁,b₂)] = −½hb₁²(1/3 − 1) = hb₁²/3 ≠ 0 for h > 0, b₁ > 0; the paper's own proof (EC.44)–(EC.45), §7.2 (uniform ⇒ c_ρ = 1/3), §8 and (EC.71) (c_ρ ≤ 1) all use E[v²]
--   - generalization: V₀ has a pdf ρ on [0,1] → any probability measure V₀ on ℝ with V₀([0,1]) = 1 and c_ρ > 0; reason: the proofs use only E[v²] = c_ρ and v ∈ [0,1]; every law with a pdf on [0,1] has c_ρ > 0 and is an instance
--   - encoding: division by c_ρ(n − 1) in (19)–(20) → hypotheses n ≥ 2 and 0 < c_ρ; reason: the paper assumes n ≥ 2 (p.26); c_ρ = 0 only for V₀ = δ₀, where the mechanism is undefined
--   - encoding: users, bids b_{−i}, the allocation Σ_{t=1}^k δ_t(i) → Fin n; b ∈ [0,1]ⁿ with the i-th entry overwritten; Measure.pi with Function.update for E_{b_{−i}∼V_{−i}}; sums over injective sequences Fin t ↪ Fin n; reason: Lean convention; same instances
--   - encoding: expectations in U-BNIC and U-SP written without integrability → U-BNIC and U-SP require the integrands to be integrable; reason: only excludes undefined expectations; for Mechanism 3 the integrands are bounded and continuous on [0,1]ⁿ
--   - reading: 1-SCP (Definition 6, c = 1) → IsOneSCP: the miner and user i cannot raise u_i + r̃ by changing user i's bid, ex post, for every b_{−i}, v, x ∈ [0,1]; reason: the paper's deviation MU₁-UB (Table 2), characterized by Lemma EC.3
--   - reading: (C, O(1/(1−C)))-U-SP → ∃ K absolute (chosen before λ₀, k, V₀, the h_η and C) such that the mechanism is (C, K/(1−C))-U-SP for every C ∈ [0,1); reason: the strongest reading of O(·); the paper's route gives K = 4
--   - reading: 'the mechanism' in the U-SP clause, a variable-bid-size TFM (Definition 1′) → Mechanism 3 at every bid count η with m_#(λ₀) and any h_η in the h-range at η; U-SP required for n ≥ max{λ₀k, 30}; reason: the h-range defining the mechanism exists only for η ≥ max{λ₀k, 30}; every admissible family is covered
--   - encoding: "any block size k" (k transactions confirmed per block) → hypothesis 1 ≤ k in (A), (B) and (C); reason: a block confirms at least one transaction; at k = 0 the allocation (25) is the empty sum 0 and Mechanism 3's division by a_i is undefined (p.29: every a_i > 0)
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §6.2, Theorem 4 (Main Theorem), pp.29–30 (Mechanism 3 p.29; proof Appendix EC.4.4, pp.ec17–ec25)

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Properties
import Definitions.Def_BlockchainTFM_Mechanism3
import Definitions.Def_BlockchainTFM_Constants

open MeasureTheory

namespace BlockchainTFM

/-- **Theorem 4 (Main Theorem)**, Chen–Simchi-Levi–Zhao–Zhou, *Bayesian Mechanism Design for
Blockchain Transaction Fee Allocation*, arXiv:2209.13099v7, pp.29–30, with `c_ρ = E[v²]`.

(A) For any block size `k ≥ 1`, any number of users `n ≥ 2` and any parameters
`m, h ∈ [0, +∞)`, Mechanism 3 `M̃ = (a, p̃, r̃)` is U-BNIC and 1-SCP.

(B) For any fixed `λ₀ > e/(e−1) ≈ 1.582` and any `n ≥ max{λ₀k, 30}`, with
`m = m_#(λ₀) = min{½ ln(1/ln(λ₀/(λ₀−1))), 1}` and every `h ∈ [0, g(λ₀) 2kc_ρ(n−1)/(en²)]`,
Mechanism 3 is UIR and BF.

(C) Furthermore, the mechanism is `(C, O(1/(1−C)))`-U-SP for every `C ∈ [0,1)`: there is an
absolute constant `K` such that for every `λ₀ > e/(e−1)`, `k ≥ 1`, law `V₀`, every choice of
`h_η` in the range of (B) for each bid count `η ≥ max{λ₀k, 30}` and every `C ∈ [0,1)`, the
variable-bid-size TFM that runs Mechanism 3 with `m_#(λ₀)` and `h_η` on `η` bids is
`(C, K/(1−C))`-U-SP on bid counts `n ≥ max{λ₀k, 30}`.

**Formalization Note.** Valuations are i.i.d. from any probability measure `V₀` on `ℝ` carried
by `[0,1]` with `c_ρ = crho V₀ = ∫ t² dV₀ > 0` (the paper's (18) prints `∫ρ²`; corrected).
`n ≥ 2` and `c_ρ > 0` make the mechanism's division by `c_ρ(n−1)` meaningful. U-BNIC and U-SP
include the existence (integrability) of the expectations. -/
theorem theorem_4 :
    (∀ (n k : ℕ), 2 ≤ n → 1 ≤ k → ∀ (V₀ : Measure ℝ), IsProbabilityMeasure V₀ →
      V₀ (Set.Icc 0 1) = 1 → 0 < crho V₀ → ∀ m h : ℝ, 0 ≤ m → 0 ≤ h →
        IsUBNIC V₀ (mech3 n k m h (crho V₀)) ∧ IsOneSCP (mech3 n k m h (crho V₀))) ∧
    (∀ lam0 : ℝ, Real.exp 1 / (Real.exp 1 - 1) < lam0 → ∀ (n k : ℕ), 1 ≤ k →
      max (lam0 * k) 30 ≤ (n : ℝ) → ∀ (V₀ : Measure ℝ), IsProbabilityMeasure V₀ →
      V₀ (Set.Icc 0 1) = 1 → 0 < crho V₀ → ∀ h ∈ Set.Icc 0 (hMax lam0 k (crho V₀) n),
        IsUIR (mech3 n k (mSharp lam0) h (crho V₀)) ∧
          IsBF (mech3 n k (mSharp lam0) h (crho V₀))) ∧
    (∃ K : ℝ, ∀ lam0 : ℝ, Real.exp 1 / (Real.exp 1 - 1) < lam0 → ∀ k : ℕ, 1 ≤ k →
      ∀ (V₀ : Measure ℝ), IsProbabilityMeasure V₀ → V₀ (Set.Icc 0 1) = 1 → 0 < crho V₀ →
      ∀ hfam : ℕ → ℝ, (∀ η : ℕ, max (lam0 * k) 30 ≤ (η : ℝ) →
          hfam η ∈ Set.Icc 0 (hMax lam0 k (crho V₀) η)) →
      ∀ C ∈ Set.Ico (0 : ℝ) 1,
        IsUSP V₀ (fun η => mech3 η k (mSharp lam0) (hfam η) (crho V₀)) C (K / (1 - C))
          (max (lam0 * k) 30)) := by sorry

end BlockchainTFM
