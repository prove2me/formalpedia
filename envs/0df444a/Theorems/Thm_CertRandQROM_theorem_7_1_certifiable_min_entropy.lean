-- Prove2me | Theorems.Thm_CertRandQROM_theorem_7_1_certifiable_min_entropy
-- name    : CertRandQROM.theorem_7_1_certifiable_min_entropy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:59.18718+00:00
-- url     : https://prove2.me/theorems/f0bd0db7-963f-4f42-9733-99d2a549b639
-- title:
--   Theorem 7.1 (Certifiable Min-Entropy) — Construction 6.2 certifies $\lceil\lambda^c/3\rceil$ bits against $2^{o(\lambda^c)}$-query adversaries
-- statement:
--   Construction 6.2 (relative to a biased random oracle) satisfies $(Q,h_\infty)$-certifiable min-entropy (Definition 6.1) for every constant $c\in(0,\tfrac12)$, any $Q=2^{o(\lambda^c)}$ and $h_\infty(\lambda)=\lceil\lambda^c/3\rceil$. Explicitly: let $C_\lambda$ be the code of §5.2 and $H$ the $p$-biased oracle on $[n]\times\Sigma_\lambda$ with the bias $p$ of §6.2. For every (unbounded) adversary $\mathcal A=(\mathcal A_\lambda)$ making at most $Q(\lambda)$ queries and every $t\in\mathbb N$ there is a negligible function $\nu$ such that for all $\lambda$
--
--   $$
--   \Pr_H\Big[\Pr\big[\mathrm{Verify}^H(\mathcal A^H)\ne\bot\big]\ge\lambda^{-t}\ \wedge\ H_\infty\big(\mathcal A^H_\top\big)\le\lceil\lambda^c/3\rceil\Big]\le\nu(\lambda).
--   $$
--
--   This is the paper's main result: an adversary that makes the classical verifier accept with noticeable probability must output strings carrying $\lceil\lambda^c/3\rceil$ bits of min-entropy conditioned on the oracle, without any structured (e.g. permutation or trapdoor) assumption, unconditionally in the random oracle model.
--
--   **Formalization Note** The field family and generators are parameters ($|F_\lambda|=2^{2\lfloor\log_2\lambda\rfloor}$, $\gamma_\lambda$ of order $|F_\lambda|-1$ for $\lambda\ge2$). An adversary at $\lambda$ is a `QueryAlg` with any finite work register $W_\lambda$, any initial state, unitaries and POVM, making $Q_a(\lambda)\le Q(\lambda)$ queries, with outputs `Option (Σ^n)` (`none` is $\bot$ or an unparseable string). $Q=2^{o(\lambda^c)}$ is: for every $\varepsilon>0$, eventually $Q(\lambda)\le2^{\varepsilon\lambda^c}$. $\Pr_H$ is the published `ErasureQTanner.noisyProb` of the $p$-biased product law. "Negligible" is the published `CommitOpen.Benign.Negligible` ($\forall c$, eventually $|\nu(m)|\le m^{-c}$). $\nu$ may depend on the adversary, as in Definition 6.1.
--
--   Differences from the source:
--   - generalization: the field F_{q(λ)} with q(λ) = 2^{2⌊log λ⌋} and an arbitrary generator γ(λ) of F_q^* → any field family F with |F λ| = 2^{2⌊log₂ λ⌋} and any γ λ of order |F λ| − 1, for λ ≥ 2; reason: every field with q elements is isomorphic to F_q; the paper's choice is one instance
--   - encoding: FRS evaluation points γ^{jm+1}, …, γ^{jm+m} → TFNPRom.foldedRS evaluation points γ^{jm}, …, γ^{jm+m−1}; reason: the two codes are equal as sets (f ↦ f(γ·) preserves degree); proved in the sanity file
--   - encoding: log λ → Nat.log 2 λ (⌊log₂ λ⌋), Real.logb 2; reason: base 2, as n(λ) = 2^{⌊log λ⌋} − 1 = Θ(λ) requires
--   - generalization: the measurement M of the adversary → any POVM; reason: a POVM includes every projective measurement
--   - encoding: adversary output π, Verify parses it; A_⊤^H the output of Verify conditioned on ≠ ⊥ → outputs Option (Σ^n), accProb and condOut; reason: an adversary with any finite outcome set reduces to this one by grouping its POVM elements by Verify's answer
--   - encoding: "makes at most Q quantum queries" → Qa λ ≤ Q λ queries; reason: an algorithm with fewer queries is a QueryAlg with Qa λ queries
--   - encoding: any inverse-polynomial δ(·) (footnote 5: ∀ t ∈ ℕ, δ(λ) = λ^{−t}) → ∀ t : ℕ, δ = (λ^t)⁻¹; reason: footnote 5
--   - encoding: Q(λ) = 2^{o(λ^c)} → ∀ ε > 0, eventually Q(λ) ≤ 2^{ε λ^c}; reason: definition of little-o in the exponent
--   - encoding: negl(·); the probability over H → CommitOpen.Benign.Negligible ν; ErasureQTanner.noisyProb (biasP n) of Event1 (published p-biased product law); reason: standard definition; finite sum over all oracles
--   - encoding: h∞(λ) = ⌈λ^c/3⌉; bias 1/(80√n) < p ≤ 1/(40√n) a power of 1/2 → ⌈λ^c/3⌉₊; biasP n; reason: same values (the bias proved in the sanity file)
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Theorem 7.1 (Certifiable Min-Entropy), p.38 (PDF p.40); Definition 6.1 with footnote 5, p.28 (PDF p.30); Construction 6.2, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model
import Definitions.Def_CertRandQROM_code
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_CertRandQROM_biasP
import Definitions.Def_CertRandQROM_Event1

namespace CertRandQROM

open Filter

/-- **Theorem 7.1 (Certifiable Min-Entropy)** (Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal,
*Unconditional Certified Randomness without Structure*, arXiv:2608.31112 (sha256 b75095a2…),
p.38): Construction 6.2, relative to the `p`-biased random oracle on `[n] × Σ`, satisfies
`(Q, h∞)`-certifiable min-entropy (Definition 6.1, p.28) for every constant `c ∈ (0, 1/2)`, any
`Q = 2^{o(λ^c)}` and `h∞(λ) = ⌈λ^c/3⌉`.

Unfolded (Definition 6.1 with footnote 5): for every adversary family `A = (A_λ)` making at most
`Q(λ)` queries and every `t ∈ ℕ` (`δ(λ) = λ^{−t}`), there is a negligible `ν` with
`Pr_H[Pr[Verify^H(A^H) ≠ ⊥] ≥ δ(λ) ∧ H∞(A_⊤^H) ≤ h∞(λ)] ≤ ν(λ)` for all `λ`.

**Formalization Note** Probabilities over `H` are the published `ErasureQTanner.noisyProb p` (the `p`-biased product law, `true` = value `1` with probability `p`). The code is the §5.2 family for any field family with
`|F λ| = 2^{2⌊log₂ λ⌋}` and any generators `γ λ` (for `λ ≥ 2`); `p = biasP n`. An adversary at
`λ` is a `QueryAlg` with any finite work register `W λ`, any initial state, unitaries and POVM,
and `Qa λ ≤ Q λ` queries; its outputs are `Option (Σ^n)` (`none` = `⊥`/unparseable). `Q = 2^{o(λ^c)}`
is `∀ ε > 0`, eventually `Q(λ) ≤ 2^{ε λ^c}`; negligible is `CommitOpen.Benign.Negligible`. -/
theorem theorem_7_1_certifiable_min_entropy (F : ℕ → Type) [∀ l, Field (F l)]
    [∀ l, Fintype (F l)] [∀ l, DecidableEq (F l)]
    (hF : ∀ l, 2 ≤ l → Fintype.card (F l) = 2 ^ (2 * Nat.log 2 l))
    (γ : ∀ l, F l) (hγ : ∀ l, 2 ≤ l → orderOf (γ l) = Fintype.card (F l) - 1)
    (c : ℝ) (hc₀ : 0 < c) (hc₁ : c < 1 / 2)
    (Q : ℕ → ℕ) (hQ : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, (Q l : ℝ) ≤ (2 : ℝ) ^ (ε * (l : ℝ) ^ c))
    (W : ℕ → Type) [∀ l, Fintype (W l)] [∀ l, DecidableEq (W l)] (Qa : ℕ → ℕ)
    (hQa : ∀ l, Qa l ≤ Q l)
    (A : ∀ l, QueryAlg (Dom F l) (W l) (Option (Fin (nPar F l) → Alph F l)) (Qa l)) (t : ℕ) :
    ∃ ν : ℕ → ℝ, CommitOpen.Benign.Negligible ν ∧ ∀ l : ℕ,
      ErasureQTanner.noisyProb (biasP (nPar F l))
          (fun h => Event1 (code F γ l) (A l) ((l : ℝ) ^ t)⁻¹ ⌈(l : ℝ) ^ c / 3⌉₊ h) ≤ ν l := by sorry

end CertRandQROM
