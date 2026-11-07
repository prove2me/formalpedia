-- Prove2me | Theorems.Thm_CertRandQROM_lemma_4_3_reprogramming
-- name    : CertRandQROM.lemma_4_3_reprogramming
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:14.089683+00:00
-- url     : https://prove2.me/theorems/7fabf6b6-abc9-45d0-98d9-f6ef3ce558ef
-- title:
--   Lemma 4.3 — reprogramming outside a small set keeps $k$ inputs of $M$ heavily queried
-- statement:
--   Let $M$ be a non-empty set of inputs, $h$ an oracle and $\beta>0$ such that $\tilde w_u(h)\ge\beta$ for every $u\in M$. Then for every $k\in\mathbb N$ with $1+\binom k2\le|M|$ there is a set $A_k\subseteq M$ with $|A_k|\le\binom k2$ such that for every oracle $h'\in\mathcal F_h(M\setminus A_k)$, i.e. $h'=h\oplus X$ with $X\subseteq M\setminus A_k$,
--
--   $$
--   \#\Big\{u\in M:\tilde w_u(h')\ge\frac{\beta}{(8Q|M|)^2}\Big\}\ge k .
--   $$
--
--   In the proof of Lemma 7.4 this produces exponentially many oracles under which the adversary still heavily queries the same string.
--
--   Differences from the source:
--   - generalization: inputs (i, x) ∈ [n] × Σ → inputs u of any finite type U; reason: taking U = Fin n × Σ gives the paper's statement
--   - generalization: A parametrized by Q ≥ 1 (§3.2) → any Q : ℕ; reason: at Q = 0 every total query norm is 0, so the hypothesis β ≤ w̃ with β > 0 fails on the non-empty M and the statement is vacuous; for Q ≥ 1 it is the paper's
--   - encoding: H' ∈ F_H(M ∖ A_k); "query norm" → ∀ X ⊆ M \ A_k, flipOn h X; totalQueryNorm; reason: definition of F_H; the lemma's query norms are total query norms (proof, p.19)
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 4.3, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm
import Definitions.Def_CertRandQROM_flipOn

namespace CertRandQROM

/-- **Lemma 4.3** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…), p.19): let `M` be a
non-empty set of inputs, `h` an oracle and `β > 0` with `w̃_u(h) ≥ β` for every `u ∈ M`. Then for
every `k ∈ ℕ` with `1 + (k choose 2) ≤ |M|` there is `A_k ⊆ M` with `|A_k| ≤ (k choose 2)` such
that for every oracle `h' ∈ F_h(M ∖ A_k)`, i.e. `h' = h ⊕ X` with `X ⊆ M ∖ A_k`, at least `k`
inputs of `M` receive total query norm `≥ β/(8Q|M|)²` from `A^{h'}`. -/
theorem lemma_4_3_reprogramming {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (M : Finset U)
    (hM : M.Nonempty) (h : U → Bool) (β : ℝ) (hβ : 0 < β)
    (hMβ : ∀ u ∈ M, β ≤ totalQueryNorm A h u) (k : ℕ) (hk : 1 + k.choose 2 ≤ M.card) :
    ∃ Ak : Finset U, Ak ⊆ M ∧ Ak.card ≤ k.choose 2 ∧
      ∀ X : Finset U, X ⊆ M \ Ak →
        k ≤ (M.filter fun u =>
          β / (8 * (Q : ℝ) * (M.card : ℝ)) ^ 2 ≤ totalQueryNorm A (flipOn h X) u).card := by sorry

end CertRandQROM
