-- Prove2me | Theorems.Thm_CertRandQROM_lemma_7_4_no_heavy_correct
-- name    : CertRandQROM.lemma_7_4_no_heavy_correct
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:58.525204+00:00
-- url     : https://prove2.me/theorems/f9e0ff43-0584-4ee7-8dc4-00e82c88ff61
-- title:
--   Lemma 7.4 — query-bounded adversaries do not heavily query a correct answer, except with probability $L(1-p)^{4n/5}$
-- statement:
--   Let $c\in(0,\tfrac12)$ and $t\in\mathbb N$, $\delta(\lambda)=\lambda^{-t}$, let $\alpha(\lambda)\ge\delta(\lambda)\cdot2^{-\lceil\lambda^c/3\rceil}$ and $Q(\lambda)=2^{o(\lambda^c)}$, and let $\mathcal A$ make at most $Q$ queries. Then for sufficiently large $\lambda$, with probability at least $1-L\cdot(1-p)^{4n/5}$ over the $p$-biased oracle $H$ ($p$ the bias of §6.2), every correct $x$ ($x\in C$ and $H(x)=0$) has a set $I\subseteq[n]$ with $|I|=\lceil n/10\rceil$ and
--
--   $$
--   \tilde w_{i,x_i}(H)<\frac{\alpha}{4n}\qquad\text{for all } i\in I .
--   $$
--
--   Equivalently, $\Pr_H[\neg\,\mathrm{Event2}]\le L\cdot(1-p)^{4n/5}$ with $s=\lceil n/10\rceil$. This is where the query bound $2^{o(\lambda^c)}$ enters the min-entropy proof.
--
--   **Formalization Note** $\Pr_H$ is the published `ErasureQTanner.noisyProb p` (the $p$-biased product law, $h(u)=1$ with probability $p$). $L$ is any function for which $C_\lambda$ is $(1-\tfrac{1}{5\sqrt n},\lceil2^{\lambda^c}\rceil,L(\lambda))$-list recoverable for large $\lambda$ (Lemma 5.2 provides one). The threshold is chosen before the algorithm. $(1-p)^{4n/5}$ is a real power.
--
--   Differences from the source:
--   - generalization: the field F_{q(λ)} with q(λ) = 2^{2⌊log λ⌋} and an arbitrary generator γ(λ) of F_q^* → any field family F with |F λ| = 2^{2⌊log₂ λ⌋} and any γ λ of order |F λ| − 1, for λ ≥ 2; reason: every field with q elements is isomorphic to F_q; the paper's choice is one instance
--   - generalization: L = L(λ) of Lemma 5.2 → any L : ℕ → ℕ for which C_λ is (1 − 1/(5√n), ⌈2^{λ^c}⌉, L(λ))-list recoverable for large λ; reason: Lemma 5.2's L is such a function, and the proof uses only this property
--   - generalization: A fixed (any algorithm making at most Q queries), then "for sufficiently large λ" → ∃ λ₀ before the algorithm: one threshold for all algorithms at λ with at most Q(λ) queries; reason: the proof's thresholds depend only on c, t, α, Q (§7.3, p.45: β depends only on (λ, Q, h∞, δ)); the uniform statement implies the paper's
--   - generalization: A an adversary of Construction 6.2 → any QueryAlg on [n] × Σ_λ with any finite outcome set; reason: the condition does not involve outputs
--   - encoding: with probability at least 1 − L(1 − p)^{4n/5}, H satisfies the condition → ErasureQTanner.noisyProb p (¬ Event2 … ⌈n/10⌉) ≤ L (1 − p)^{4n/5}; reason: complement of a finite event
--   - encoding: Q(λ) = 2^{o(λ^c)} → ∀ ε > 0, eventually Q(λ) ≤ 2^{ε λ^c}; reason: definition of little-o in the exponent
--   - encoding: δ(λ) = λ^{−t}, α(λ) ≥ δ(λ)·2^{−⌈λ^c/3⌉} → α λ ≥ (λ^t)⁻¹ · (2^{⌈λ^c/3⌉})⁻¹ for every λ; reason: same inequality; reals
--   - encoding: FRS evaluation points γ^{jm+1}, …, γ^{jm+m} → TFNPRom.foldedRS evaluation points γ^{jm}, …, γ^{jm+m−1}; reason: the two codes are equal as sets (f ↦ f(γ·) preserves degree); proved in the sanity file
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 7.4, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_CertRandQROM_code
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_CertRandQROM_biasP
import Definitions.Def_CertRandQROM_Event2
import Definitions.Def_TFNPRom_IsListRecoverable

namespace CertRandQROM

open Filter

/-- **Lemma 7.4** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…), p.41): for every
constant `c ∈ (0, 1/2)` and `t ∈ ℕ`, with `δ(λ) = λ^{−t}`, any `α(λ) ≥ δ(λ) 2^{−⌈λ^c/3⌉}` and any
`Q(λ) = 2^{o(λ^c)}`: for sufficiently large `λ`, for every quantum query algorithm `A` making at
most `Q` queries, with probability at least `1 − L (1 − p)^{4n/5}` over the `p`-biased oracle
`H` (`p` the bias of §6.2), `H` satisfies Event2 with `s = ⌈n/10⌉`: every correct `x`
(`x ∈ C`, `H(x) = 0`) has a set `I ⊆ [n]`, `|I| = ⌈n/10⌉`, with `w̃_{i,x_i}(H) < α/(4n)` on `I`.
Written as the bad-set bound `Pr_H[¬ Event2] ≤ L (1 − p)^{4n/5}`.

**Formalization Note** Probabilities over `H` are the published `ErasureQTanner.noisyProb p` (the `p`-biased product law, `true` = value `1` with probability `p`). `L` is any function for which `C_λ` is
`(1 − 1/(5√n), ⌈2^{λ^c}⌉, L(λ))`-list recoverable for large `λ` (the paper's `L` is Lemma 5.2's,
which is such a function). The threshold `λ₀` is chosen before the algorithm. `(1 − p)^{4n/5}` is
a real power. -/
theorem lemma_7_4_no_heavy_correct (F : ℕ → Type) [∀ l, Field (F l)] [∀ l, Fintype (F l)]
    [∀ l, DecidableEq (F l)] (hF : ∀ l, 2 ≤ l → Fintype.card (F l) = 2 ^ (2 * Nat.log 2 l))
    (γ : ∀ l, F l) (hγ : ∀ l, 2 ≤ l → orderOf (γ l) = Fintype.card (F l) - 1)
    (c : ℝ) (hc₀ : 0 < c) (hc₁ : c < 1 / 2) (t : ℕ) (α : ℕ → ℝ)
    (hα : ∀ l : ℕ, ((l : ℝ) ^ t)⁻¹ * ((2 : ℝ) ^ ⌈(l : ℝ) ^ c / 3⌉₊)⁻¹ ≤ α l)
    (Q : ℕ → ℕ) (hQ : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, (Q l : ℝ) ≤ (2 : ℝ) ^ (ε * (l : ℝ) ^ c))
    (L : ℕ → ℕ) (hL : ∃ l₁ : ℕ, ∀ l ≥ l₁, TFNPRom.IsListRecoverable (code F γ l)
      (1 - 1 / (5 * Real.sqrt (nPar F l))) ⌈(2 : ℝ) ^ ((l : ℝ) ^ c)⌉₊ (L l)) :
    ∃ l₀ : ℕ, ∀ l ≥ l₀, ∀ (W : Type) [Fintype W] [DecidableEq W] (O : Type) [Fintype O]
      (Qa : ℕ), Qa ≤ Q l → ∀ A : QueryAlg (Dom F l) W O Qa,
        ErasureQTanner.noisyProb (biasP (nPar F l))
            (fun h => ¬ Event2 (code F γ l) A (α l) ⌈(nPar F l : ℝ) / 10⌉₊ h) ≤
          (L l : ℝ) * (1 - biasP (nPar F l)) ^ (4 * (nPar F l : ℝ) / 5) := by sorry

end CertRandQROM
