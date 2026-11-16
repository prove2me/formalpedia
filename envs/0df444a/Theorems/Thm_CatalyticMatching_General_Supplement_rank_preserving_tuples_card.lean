-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_rank_preserving_tuples_card
-- name    : CatalyticMatching.General.Supplement.rank_preserving_tuples_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:55.3762+00:00
-- url     : https://prove2.me/theorems/73ead163-3882-4af6-9870-845ec8682bd3
-- title:
--   Lemma 5.2 — few replacement tuples preserve the rank when one raises it
-- statement:
--   Let $F$ be a field, $A_1,\dots,A_m\in F^{n\times n}$, $a\in F^m$, and $S\subseteq F$ finite with $|S|=n^c$. Let $I=\{i_1,\dots,i_\ell\}\subseteq[m]$ have $\ell$ elements and suppose some $\lambda\in S^{I}$ satisfies
--
--   $$\operatorname{rank}\Big(\sum_{i\in[m]\setminus I}A_ia_i+\sum_{i\in I}A_i\lambda_i\Big)>\operatorname{rank}\Big(\sum_{i\in[m]}A_ia_i\Big).$$
--
--   Let $\mathcal I_{a,I}$ be the set of $\lambda'\in S^{I}$ for which the left-hand rank, with $\lambda'$ in place of $\lambda$, equals $\operatorname{rank}\sum_iA_ia_i$. Then
--
--   $$|\mathcal I_{a,I}|\le n^{c\ell-c+1}.$$
--
--   The tuple $a$ is arbitrary in $F^m$. In the algorithm of Theorem 5.4 this bound lets the $\ell$ coordinates $a_I$ be replaced by their index in $\mathcal I_{a,I}$, freeing space.
--
--   Differences from the source:
--   - generalization: ε ∈ (0,1) fixed, ℓ = ⌈1/ε−1⌉, m ≥ ℓ, c a constant depending on ε, F a sufficiently large field → any field, any naturals ℓ and c, any I with |I| = ℓ (so m ≥ ℓ), any S with |S| = n^c; reason: the proof uses only the Schwartz–Zippel bound for a nonzero polynomial of degree ≤ n on S^ℓ; the source parameters are a special case
--   - encoding: tuples (λ_{i_1},…,λ_{i_ℓ}) ∈ S^ℓ → functions I → F with all values in S; reason: I is a set of ℓ indices; these are the same tuples
--   - encoding: exponent cℓ − c + 1 → c * ℓ - c + 1 in ℕ; reason: exact for ℓ ≥ 1; ℓ = 0 forces I = ∅, which makes the strict rank increase impossible
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 5.2, printed/PDF p.27

import Definitions.Def_CatalyticMatching_General_Supplement_MatrixSpace

namespace CatalyticMatching.General.Supplement

/-- Lemma 5.2 p.27. If some λ ∈ S^I strictly raises the rank, at most n^{cℓ−c+1} tuples of
S^I keep it equal. Any field, any a ∈ F^m, any ℓ = |I| and any c with |S| = n^c. -/
theorem rank_preserving_tuples_card {F : Type} [Field F] {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) (ℓ c : ℕ)
    (S : Finset F) (hS : S.card = n ^ c) (I : Finset (Fin m)) (hI : I.card = ℓ)
    (lam : I → F) (hlam : ∀ i, lam i ∈ S)
    (hinc : (pencil A a).rank < (pencil A (replaceCoords a I lam)).rank) :
    (rankPreservingTuples A a I S).card ≤ n ^ (c * ℓ - c + 1) := by sorry

end CatalyticMatching.General.Supplement
