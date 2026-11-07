-- Prove2me | Theorems.Thm_CertRandQROM_lemma_5_2_code_family
-- name    : CertRandQROM.lemma_5_2_code_family
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:10.045086+00:00
-- url     : https://prove2.me/theorems/25b03e54-6997-44bd-af68-b614e551eb13
-- title:
--   Lemma 5.2 (header, item 1) — the §5.2 codes are folded linear, $n=\Theta(\lambda)$, and $(1-\tfrac{1}{5\sqrt n},\lceil2^{\lambda^c}\rceil,2^{O(\lambda^c\log\lambda)})$-list recoverable
-- statement:
--   The family $\{C_\lambda\}$ of §5.2 is a family of folded linear codes over $\Sigma_\lambda=\mathbb F_{q(\lambda)}^{m(\lambda)}$ of length $n$ with
--
--   $$
--   n=\Theta(\lambda),\qquad |\Sigma|=n^{\Theta(n)}=2^{\Theta(n\log n)},
--   $$
--
--   and for sufficiently large $\lambda$:
--
--   1. for every constant $c\in(0,\tfrac12)$, $C_\lambda$ is $(\zeta(\lambda),\ell(\lambda),L(\lambda))$-list recoverable (Definition 5.1) with $\zeta(\lambda)=1-\dfrac{1}{5\sqrt{n(\lambda)}}$, $\ell(\lambda)=\lceil 2^{\lambda^c}\rceil$ and $L(\lambda)=2^{O(\lambda^c\log\lambda)}$.
--
--   Item 1 says that knowing approximate lists for only $\sqrt n/5$ coordinates already pins a codeword down to $L$ candidates; this is what limits the number of strings an adversary can heavily query (Claim 7.5).
--
--   **Formalization Note** "Folded linear" is: $0\in C_\lambda$ and $C_\lambda$ is closed under addition and under multiplication by scalars of $F_\lambda$, for every $\lambda$. $\Theta(\cdot)$ is a pair of positive constants holding eventually. In item 1 the $O$-constant $C_0$ and the threshold are chosen after $c$, and $L(\lambda)$ is $\lfloor 2^{C_0\lambda^c\log_2\lambda}\rfloor$ (list recoverability is monotone in $L$). List recoverability is the published `TFNPRom.IsListRecoverable`. Item 2 of Lemma 5.2 (dual decoding) is not part of this statement; it serves only the correctness theorem.
--
--   Differences from the source:
--   - generalization: the field F_{q(λ)} with q(λ) = 2^{2⌊log λ⌋} and an arbitrary generator γ(λ) of F_q^* → any field family F with |F λ| = 2^{2⌊log₂ λ⌋} and any γ λ of order |F λ| − 1, for λ ≥ 2; reason: every field with q elements is isomorphic to F_q; the paper's choice is one instance
--   - encoding: FRS evaluation points γ^{jm+1}, …, γ^{jm+m} → TFNPRom.foldedRS evaluation points γ^{jm}, …, γ^{jm+m−1}; reason: the two codes are equal as sets (f ↦ f(γ·) preserves degree); proved in the sanity file
--   - encoding: log λ → Nat.log 2 λ (⌊log₂ λ⌋), Real.logb 2; reason: base 2, as n(λ) = 2^{⌊log λ⌋} − 1 = Θ(λ) requires
--   - reading: "satisfies the following for sufficiently large λ: 1. For every constant c ∈ (0, 1/2) … L(λ) = 2^{O(λ^c log λ)}" → ∀ c ∈ (0, 1/2), ∃ C₀ > 0, eventually in λ; reason: the proof's threshold depends on c (s = ⌊10λ^c⌋, ℓ = ⌈2^{λ^c}⌉), and an O(·) inside "for every constant c" may depend on c
--   - encoding: folded linear code: a linear subspace of F_q^{n·m} → 0 ∈ C_λ, closed under + and F_λ-scalar multiplication, for every λ; reason: definition of a subspace under the canonical embedding
--   - encoding: n = Θ(λ), |Σ| = n^{Θ(n)} = 2^{Θ(n log n)}, L = 2^{O(λ^c log λ)} → positive constants a, b (resp. C₀) with the bounds holding eventually; L = ⌊2^{C₀ λ^c log₂ λ}⌋; reason: definitions of Θ and O; list recoverability is monotone in L
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 5.2, header and item 1, p.23 (PDF p.25); construction §5.2, p.23

import Mathlib
import Definitions.Def_CertRandQROM_code
import Definitions.Def_TFNPRom_IsListRecoverable

namespace CertRandQROM

open Filter

/-- **Lemma 5.2, header and item 1** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…),
p.23; adapted from [YZ24, Lemma 4.2]): the family `{C_λ}` of §5.2 is a family of folded linear
codes over `Σ_λ = F_{q(λ)}^{m(λ)}` of length `n` with `n = Θ(λ)` and
`|Σ| = n^{Θ(n)} = 2^{Θ(n log n)}`, and for sufficiently large `λ`:

1. for every constant `c ∈ (0, 1/2)`, `C_λ` is `(ζ(λ), ℓ(λ), L(λ))`-list recoverable with
   `ζ(λ) = 1 − 1/(5√n(λ))`, `ℓ(λ) = ⌈2^{λ^c}⌉` and `L(λ) = 2^{O(λ^c log λ)}`.

The field family `F` has `|F λ| = 2^{2⌊log₂ λ⌋}` and `γ λ` generates `(F λ)^*`, for `λ ≥ 2`.

**Formalization Note** "Folded linear" is: `0 ∈ C_λ` and `C_λ` is closed under addition and
under multiplication by scalars of `F λ` (a subspace of `F^{n·m}` under the canonical
embedding), for every `λ`. `Θ(·)` is two-sided constants holding eventually. In item 1 the
threshold and the `O`-constant `C₀` are chosen after `c`, and `L(λ)` is
`⌊2^{C₀ λ^c log₂ λ}⌋` (list recoverability is monotone in `L`). Item 2 (dual decoding) is not
part of this statement. -/
theorem lemma_5_2_code_family (F : ℕ → Type) [∀ l, Field (F l)] [∀ l, Fintype (F l)]
    [∀ l, DecidableEq (F l)] (hF : ∀ l, 2 ≤ l → Fintype.card (F l) = 2 ^ (2 * Nat.log 2 l))
    (γ : ∀ l, F l) (hγ : ∀ l, 2 ≤ l → orderOf (γ l) = Fintype.card (F l) - 1) :
    (∀ l, 0 ∈ code F γ l ∧ (∀ x ∈ code F γ l, ∀ y ∈ code F γ l, x + y ∈ code F γ l) ∧
        ∀ a : F l, ∀ x ∈ code F γ l, a • x ∈ code F γ l) ∧
      (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ l : ℕ in atTop,
        a * (l : ℝ) ≤ (nPar F l : ℝ) ∧ (nPar F l : ℝ) ≤ b * (l : ℝ)) ∧
      (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ l : ℕ in atTop,
        (nPar F l : ℝ) ^ (a * (nPar F l : ℝ)) ≤ (Fintype.card (Alph F l) : ℝ) ∧
          (Fintype.card (Alph F l) : ℝ) ≤ (nPar F l : ℝ) ^ (b * (nPar F l : ℝ))) ∧
      (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ l : ℕ in atTop,
        (2 : ℝ) ^ (a * (nPar F l : ℝ) * Real.logb 2 (nPar F l)) ≤ (Fintype.card (Alph F l) : ℝ) ∧
          (Fintype.card (Alph F l) : ℝ) ≤ (2 : ℝ) ^ (b * (nPar F l : ℝ) * Real.logb 2 (nPar F l))) ∧
      ∀ c : ℝ, 0 < c → c < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ l : ℕ in atTop,
        TFNPRom.IsListRecoverable (code F γ l) (1 - 1 / (5 * Real.sqrt (nPar F l)))
          ⌈(2 : ℝ) ^ ((l : ℝ) ^ c)⌉₊ ⌊(2 : ℝ) ^ (C₀ * (l : ℝ) ^ c * Real.logb 2 l)⌋₊ := by sorry

end CertRandQROM
