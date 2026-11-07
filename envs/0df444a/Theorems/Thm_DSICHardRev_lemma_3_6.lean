-- Prove2me | Theorems.Thm_DSICHardRev_lemma_3_6
-- name    : DSICHardRev.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:05.967704+00:00
-- url     : https://prove2.me/theorems/0fe58e35-822b-4e91-9593-c2be76c865cd
-- title:
--   Lemma 3.6 — welfare bound on a general-valuation KSSHD instance
-- statement:
--   Let $\mathcal H$ be an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD on $m$ items for general valuations. For every instance drawn from $\mathcal H$ and every allocation $(S_1,\dots,S_n)$,
--   $$\sum_{i\in[n]}v_i(S_i)\;\le\;\frac{2m}{\eta}+2\alpha\sum_{k\in[\kappa]}\mathbb 1(S_{i_k}\supseteq A_k)\;\le\;\frac{2m}{\eta}+2\sum_{k\in[\kappa]}|S_{i_k}\cap A_k|.$$
--
--   Both inequalities of the chain are asserted. It is the general-valuation counterpart of Lemma 3.5.
--
--   Differences from the source:
--   - encoding: an instance drawn from the KSSHD → any valid sample (j, ϑ, φ) in the support; reason: the support of the distribution of Properties (5)–(12)
--   - reading: all relevant quantities are integers (p.7) → α, η, λ, β = m/η, κ = m/(2α) natural numbers with β·η = m and κ·(2α) = m; reason: the paper's standing integrality convention
--   - encoding: the distribution of Properties (5)–(12) → the uniform law on valid samples (j, ϑ, φ), m ≥ 1, κα + β − α ≤ m; reason: the same law (every choice of A, B admits the same number of bijections); m ≥ 1 excludes the empty auction with no groups, and the size condition is exactly that the sets of Property (7) exist
--   - reading: u_x is either (a) or (b) for each x → one branch (GS, XOS or general) for all x; reason: a KSSHD "using GS valuations" / "for general valuations" is how the paper uses the definition
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.14, Lemma 3.6

import Mathlib
import Definitions.Def_DSICHardRev_KSSHD

namespace DSICHardRev

/-- **Lemma 3.6** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.14):
for any allocation `(S_1, …, S_n)` on an instance drawn from an `(α, η, λ, C, U)`-KSSHD for general
valuations, `∑_i v_i(S_i) ≤ 2m/η + 2α ∑_k 1(S_{i_k} ⊇ A_k) ≤ 2m/η + 2 ∑_k |S_{i_k} ∩ A_k|`.

**Formalization Note.** Both inequalities of the chain are stated. "An instance drawn from" the
KSSHD is any valid sample `ω`. -/
theorem lemma_3_6 {m : ℕ} (H : KSSHD m) (hb : H.branch = .gen)
    (ω : H.Sample) (hω : H.Valid ω) (S : H.Bidder → Finset (Fin m))
    (hS : Pairwise fun a b => Disjoint (S a) (S b)) :
    ∑ b, H.val ω b (S b) ≤
        2 * (m : ℝ) / H.η + 2 * (H.α : ℝ) * ∑ k, (if H.A ω k ⊆ S (H.ik ω k) then (1 : ℝ) else 0) ∧
      2 * (m : ℝ) / H.η + 2 * (H.α : ℝ) * ∑ k, (if H.A ω k ⊆ S (H.ik ω k) then (1 : ℝ) else 0) ≤
        2 * (m : ℝ) / H.η + 2 * ∑ k, ((S (H.ik ω k) ∩ H.A ω k).card : ℝ) := by sorry

end DSICHardRev
