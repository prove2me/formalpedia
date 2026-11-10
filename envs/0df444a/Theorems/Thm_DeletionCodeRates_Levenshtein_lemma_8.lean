-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_lemma_8
-- name    : DeletionCodeRates.Levenshtein.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:20:39.684707+00:00
-- url     : https://prove2.me/theorems/c385f964-9b0e-4f83-a3dd-17bf9b986657
-- title:
--   Lemma 8 — common-witness sampling lemma
-- statement:
--   Fix $L\ge1$. For each $n$ let $P_n$ be a distribution on a finite set $\mathcal X_n$, and let $\mathcal W_n(\boldsymbol c)$ be a nonempty set of witnesses for each $\boldsymbol c\in\mathcal X_n$. Suppose independent samples $\boldsymbol C_1,\dots,\boldsymbol C_{L+1}$ satisfy
--   $$\Pr\Big[\textstyle\bigcap_{i=1}^{L+1}\mathcal W_n(\boldsymbol C_i)\ne\emptyset\Big]\le2^{-n(a-o(1))}.\qquad(17)$$
--   Then for every $0<R<a/L$ and all sufficiently large $n$ there is a set $\mathcal C_n\subseteq\mathcal X_n$ of size at least $\lfloor2^{Rn}\rfloor/L$ such that every witness belongs to at most $L$ members of $\mathcal C_n$.
--
--   Differences from the source:
--   - encoding: Pr[⋂ W_n(C_i) ≠ ∅] for L+1 independent samples from P_n → commonWitnessProb (P n) (W n) (L+1), the sum over tuples f : Fin (L+1) → X n with a common witness of ∏ P n (f i); reason: the exact probability of the event under the product law on a finite set
--   - encoding: 2^{−n(a−o(1))} → ∃ ε : ℕ → ℝ, ε → 0, with the bound 2^{−n(a−ε n)} for every n; reason: o(1) made explicit; at n = 0 the bound is probability ≤ 1, and at finitely many positive n it can be met by enlarging ε n, so 'for every n' says the same as 'for all large n'
--   - encoding: witnesses of unspecified kind → a witness type Wit n for each n, with W n c : Set (Wit n); reason: the paper does not fix a witness universe; any type is allowed
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), Lemma 8, p. 9 (PDF 11)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_Sampling

set_option autoImplicit false

open Filter Topology

namespace DeletionCodeRates.Levenshtein

open Classical in
/-- **Lemma 8** (common-witness sampling lemma, p. 9). Fix `L ≥ 1`. For each `n` let `P n` be a
distribution on a finite set `X n` and `W n c` a nonempty set of witnesses for each `c ∈ X n`.
If `L + 1` independent samples have a common witness with probability at most
`2^{-n(a - o(1))}` (17), then for every `0 < R < a / L` and all sufficiently large `n` there is a
set `C_n ⊆ X n` of size at least `⌊2^{Rn}⌋ / L` such that every witness belongs to at most `L`
members of `C_n`. -/
theorem lemma_8 (L : ℕ) (hL : 1 ≤ L) (X : ℕ → Type*) [∀ n, Fintype (X n)]
    (P : ∀ n, PMF (X n)) (Wit : ℕ → Type*) (W : ∀ n, X n → Set (Wit n))
    (hW : ∀ n (c : X n), (W n c).Nonempty) (a : ℝ)
    (h17 : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, commonWitnessProb (P n) (W n) (L + 1) ≤ (2 : ℝ) ^ (-((n : ℝ) * (a - ε n)))) :
    ∀ R : ℝ, 0 < R → R < a / L → ∀ᶠ n : ℕ in atTop, ∃ C : Finset (X n),
      ((⌊(2 : ℝ) ^ (R * n)⌋₊ : ℝ) / L ≤ (C.card : ℝ)) ∧
      ∀ w : Wit n, (C.filter (fun c => w ∈ W n c)).card ≤ L := by sorry

end DeletionCodeRates.Levenshtein
