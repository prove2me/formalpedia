-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_lemma_3_8
-- name    : AgnosticImitate.Reduction.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:23:56.146083+00:00
-- url     : https://prove2.me/theorems/7b2347c2-29cc-4e08-909e-a691ecea5e0e
-- title:
--   Lemma 3.8 — loss smoothing: k_σ = E[k(N_σ(·))] is [±B]-valued and O(B/σ)-Lipschitz, ℓ_σ ≤ ℓ + O(Bσ), and |E ℓ(p, k(N_σ(q))) − ℓ_σ(p, k_σ(q))| ≤ O(Bσ)
-- statement:
--   There is a universal constant $K>0$ with the following property. Let $\ell$ be a naturally parametrized loss ($A=\mathbb R$, $\partial\ell(\eta)=-\eta$) with a $[\pm B]$-valued best-response function $k$. Then for every $\sigma>0$ with $\sigma^{-1}\in\mathbb N$ there is a naturally parametrized loss $\ell_\sigma$ with a best-response function $k_\sigma$ given by
--   $$k_\sigma(p)=\mathbb E[k(N_\sigma(p))]\qquad(p\in[-1,1]),$$
--   where $N_\sigma$ rounds its input randomly to one of the two neighbouring multiples of $\sigma$ preserving its mean, such that
--
--   - **(Smoothness)** $k_\sigma$ is $[\pm B]$-valued and $KB/\sigma$-Lipschitz on $[\pm1]$;
--   - **(Approximation)** $\ell_\sigma(p,\eta)\le\ell(p,\eta)+KB\sigma$ for all $p\in[\pm1]$, $\eta\in\mathbb R$, and $\big|\mathbb E[\ell(p,k(N_\sigma(q)))]-\ell_\sigma(p,k_\sigma(q))\big|\le KB\sigma$ for all $p,q\in[\pm1]$.
--
--   Differences from the source:
--   - encoding: a loss ℓ : {±1} × A → ℝ → ℓ : ℝ → A → ℝ, used only at y = 1 and y = −1 (expLoss); reason: the values at other y never enter
--   - encoding: O(B/σ), O(Bσ), O(Bσ) → K·B/σ, K·B·σ, K·B·σ with one universal constant K > 0 chosen before ℓ, B, k and σ; reason: an O(·) with a universal constant
--   - encoding: the randomized noise function N_σ and E[φ(N_σ(v))] → the explicit two-point average noiseExp σ φ v; reason: N_σ(v) takes the two neighbouring grid values with the stated mean-preserving probabilities; only its expectations enter
--   - encoding: σ^{−1} ∈ ℕ → 0 < σ and ∃ n : ℕ, σ⁻¹ = n; reason: same condition
--   - encoding: k_{ℓσ} is O(B/σ)-Lipschitz and [±B]-valued; k_{ℓσ}(p) = E[k_ℓ(N_σ(p))] → for p, q ∈ [−1, 1]: kσ p = noiseExp σ k p, kσ p ∈ [−B, B], |kσ p − kσ q| ≤ K B/σ |p − q|; kσ is a best response of ℓσ; reason: best responses and N_σ are defined on [±1]
--   - encoding: k_ℓ(p) ∈ argmin_a ℓ(p, a), the best-response function → a given selection k with IsBestResponse ℓ k (ℓ(p, k(p)) ≤ ℓ(p, a) for all p ∈ [−1, 1] and all a); reason: the paper's k_ℓ is a chosen selection; a best response need not exist in general, so it is assumed given
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Lemma 3.8, p. 21 (PDF 23); proof pp. 42–43 (PDF 44–45)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Losses

namespace AgnosticImitate.Reduction

/-- Lemma 3.8 (Loss Smoothing, p. 21, PDF 23). There is a universal constant `K` such that for
every naturally parametrized loss `ℓ` with a `[±B]`-valued best-response function `k` and every
`σ` with `σ⁻¹ ∈ ℕ`, there is a naturally parametrized loss `ℓ_σ` with a best-response function
`k_σ(p) = E[k(N_σ(p))]` such that `k_σ` is `[±B]`-valued and `K B/σ`-Lipschitz on `[±1]`,
`ℓ_σ(p, η) ≤ ℓ(p, η) + K B σ` for all `p ∈ [±1]`, `η ∈ ℝ`, and
`|E[ℓ(p, k(N_σ(q)))] - ℓ_σ(p, k_σ(q))| ≤ K B σ` for all `p, q ∈ [±1]`. -/
theorem lemma_3_8 :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ℓ : ℝ → ℝ → ℝ) (B : ℝ) (k : ℝ → ℝ), IsNaturallyParametrized ℓ →
        IsBestResponse ℓ k → (∀ p ∈ Set.Icc (-1 : ℝ) 1, k p ∈ Set.Icc (-B) B) →
        ∀ σ : ℝ, 0 < σ → (∃ n : ℕ, σ⁻¹ = n) →
          ∃ (ℓσ : ℝ → ℝ → ℝ) (kσ : ℝ → ℝ),
            IsNaturallyParametrized ℓσ ∧ IsBestResponse ℓσ kσ ∧
            (∀ p ∈ Set.Icc (-1 : ℝ) 1, kσ p = noiseExp σ k p) ∧
            (∀ p ∈ Set.Icc (-1 : ℝ) 1, kσ p ∈ Set.Icc (-B) B) ∧
            (∀ p ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (-1 : ℝ) 1,
              |kσ p - kσ q| ≤ K * B / σ * |p - q|) ∧
            (∀ p ∈ Set.Icc (-1 : ℝ) 1, ∀ η : ℝ, expLoss ℓσ p η ≤ expLoss ℓ p η + K * B * σ) ∧
            (∀ p ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (-1 : ℝ) 1,
              |noiseExp σ (fun v => expLoss ℓ p (k v)) q - expLoss ℓσ p (kσ q)| ≤
                K * B * σ) := by sorry

end AgnosticImitate.Reduction
