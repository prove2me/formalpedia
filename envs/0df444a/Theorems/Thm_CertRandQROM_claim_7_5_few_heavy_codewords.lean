-- Prove2me | Theorems.Thm_CertRandQROM_claim_7_5_few_heavy_codewords
-- name    : CertRandQROM.claim_7_5_few_heavy_codewords
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:29.846006+00:00
-- url     : https://prove2.me/theorems/5d0cc921-a7fc-4671-9a3e-df9b7cd221b2
-- title:
--   Claim 7.5 — at most $L$ codewords are heavily queried
-- statement:
--   Let $c\in(0,\tfrac12)$ and $t\in\mathbb N$, let $\alpha(\lambda)\ge\lambda^{-t}\cdot2^{-\lceil\lambda^c/3\rceil}$, let $Q(\lambda)=2^{o(\lambda^c)}$ with $Q\ge1$, and let $L(\lambda)$ be such that $C_\lambda$ is $(1-\tfrac{1}{5\sqrt n},\lceil2^{\lambda^c}\rceil,L(\lambda))$-list recoverable for large $\lambda$ (Lemma 5.2). Then for sufficiently large $\lambda$, for every algorithm $\mathcal A$ making at most $Q(\lambda)$ queries and every oracle $h'$,
--
--   $$
--   \#\Big\{x\in C_\lambda:\ \mathcal A^{h'}\text{ heavily queries }x\text{ at level }\frac{\alpha}{256Q^2n^3}\Big\}\le L(\lambda),
--   $$
--
--   where heavily querying $x$ means $\tilde w_{i,x_i}(h')\ge\alpha/(256Q^2n^3)$ for at least $\sqrt n/5$ coordinates $i$.
--
--   Together with Claim 7.6 this bounds the overlap of the sets $T_h$ in the proof of Lemma 7.4.
--
--   **Formalization Note** $Q=2^{o(\lambda^c)}$ is: for every $\varepsilon>0$, eventually $Q(\lambda)\le2^{\varepsilon\lambda^c}$. The level uses the query bound $Q(\lambda)\ge1$ (§3.2's standing $Q\ge1$, which keeps the level well defined); the algorithm makes $Q_a\le Q(\lambda)$ queries. The code is the §5.2 family for the given field family and generators.
--
--   Differences from the source:
--   - generalization: the field F_{q(λ)} with q(λ) = 2^{2⌊log λ⌋} and an arbitrary generator γ(λ) of F_q^* → any field family F with |F λ| = 2^{2⌊log₂ λ⌋} and any γ λ of order |F λ| − 1, for λ ≥ 2; reason: every field with q elements is isomorphic to F_q; the paper's choice is one instance
--   - generalization: L = L(λ) of Lemma 5.2 → any L : ℕ → ℕ for which C_λ is (1 − 1/(5√n), ⌈2^{λ^c}⌉, L(λ))-list recoverable for large λ; reason: Lemma 5.2's L is such a function, and the proof uses only this property
--   - generalization: A fixed (any algorithm making at most Q queries), then "for sufficiently large λ" → ∃ λ₀ before the algorithm: one threshold for all algorithms at λ with at most Q(λ) queries; reason: the proof's thresholds depend only on c, t, α, Q (§7.3, p.45: β depends only on (λ, Q, h∞, δ)); the uniform statement implies the paper's
--   - generalization: h' ∈ T_h (the oracles of the proof of Lemma 7.4) → every oracle h'; reason: the claim's proof uses nothing about h'
--   - generalization: A an adversary of Construction 6.2 → any QueryAlg on [n] × Σ_λ with any finite outcome set; reason: the claim does not involve outputs
--   - encoding: Q(λ) = 2^{o(λ^c)} → ∀ ε > 0, eventually Q(λ) ≤ 2^{ε λ^c}; reason: definition of little-o in the exponent
--   - encoding: δ(λ) = λ^{−t}, α(λ) ≥ δ(λ)·2^{−⌈λ^c/3⌉} → α λ ≥ (λ^t)⁻¹ · (2^{⌈λ^c/3⌉})⁻¹ for every λ; reason: same inequality; reals
--   - encoding: FRS evaluation points γ^{jm+1}, …, γ^{jm+m} → TFNPRom.foldedRS evaluation points γ^{jm}, …, γ^{jm+m−1}; reason: the two codes are equal as sets (f ↦ f(γ·) preserves degree); proved in the sanity file
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Claim 7.5 and the definition of "heavily queries", p.42 (PDF p.44); hypotheses of Lemma 7.4, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_CertRandQROM_code
import Definitions.Def_CertRandQROM_HeavilyQueries
import Definitions.Def_TFNPRom_IsListRecoverable

namespace CertRandQROM

open Filter

open Classical in
/-- **Claim 7.5** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…), p.42), with the
definition of heavy querying just above it and the hypotheses of Lemma 7.4 (p.41): let
`c ∈ (0, 1/2)`, `t ∈ ℕ`, `α(λ) ≥ λ^{−t} 2^{−⌈λ^c/3⌉}`, `Q(λ) = 2^{o(λ^c)}` (with `Q ≥ 1`), and
let `L(λ)` be such that `C_λ` is `(1 − 1/(5√n), ⌈2^{λ^c}⌉, L(λ))`-list recoverable for large
`λ`. Then for sufficiently large `λ`, for every algorithm `A` making at most `Q(λ)` queries and
every oracle `h'`, the number of codewords `x ∈ C_λ` that `A^{h'}` heavily queries (at least
`√n/5` coordinates `i` with `w̃_{i,x_i}(h') ≥ α/(256 Q² n³)`) is at most `L(λ)`.

**Formalization Note** `Q = 2^{o(λ^c)}` is `∀ ε > 0`, eventually `Q(λ) ≤ 2^{ε λ^c}`. The
threshold `λ₀` is chosen before the algorithm. `L` is any function with the list-recovery
property (the paper's is Lemma 5.2's). `Q ≥ 1` is §3.2's standing assumption on the query
bound; it keeps `α/(256 Q² n³)` well defined. -/
theorem claim_7_5_few_heavy_codewords (F : ℕ → Type) [∀ l, Field (F l)] [∀ l, Fintype (F l)]
    [∀ l, DecidableEq (F l)] (hF : ∀ l, 2 ≤ l → Fintype.card (F l) = 2 ^ (2 * Nat.log 2 l))
    (γ : ∀ l, F l) (hγ : ∀ l, 2 ≤ l → orderOf (γ l) = Fintype.card (F l) - 1)
    (c : ℝ) (hc₀ : 0 < c) (hc₁ : c < 1 / 2) (t : ℕ) (α : ℕ → ℝ)
    (hα : ∀ l : ℕ, ((l : ℝ) ^ t)⁻¹ * ((2 : ℝ) ^ ⌈(l : ℝ) ^ c / 3⌉₊)⁻¹ ≤ α l)
    (Q : ℕ → ℕ) (hQ₁ : ∀ l, 1 ≤ Q l)
    (hQ : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, (Q l : ℝ) ≤ (2 : ℝ) ^ (ε * (l : ℝ) ^ c))
    (L : ℕ → ℕ) (hL : ∃ l₁ : ℕ, ∀ l ≥ l₁, TFNPRom.IsListRecoverable (code F γ l)
      (1 - 1 / (5 * Real.sqrt (nPar F l))) ⌈(2 : ℝ) ^ ((l : ℝ) ^ c)⌉₊ (L l)) :
    ∃ l₀ : ℕ, ∀ l ≥ l₀, ∀ (W : Type) [Fintype W] [DecidableEq W] (O : Type) [Fintype O]
      (Qa : ℕ), Qa ≤ Q l → ∀ (A : QueryAlg (Dom F l) W O Qa) (h' : Dom F l → Bool),
        ((code F γ l).filter fun x =>
          HeavilyQueries A h' x (α l / (256 * (Q l : ℝ) ^ 2 * (nPar F l : ℝ) ^ 3))).card ≤ L l := by sorry

end CertRandQROM
