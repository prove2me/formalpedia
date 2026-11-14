-- Prove2me | Theorems.Thm_BosonicLearn_loewner_eigenvalue_pairing
-- name    : BosonicLearn.loewner_eigenvalue_pairing
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:54:57.387675+00:00
-- url     : https://prove2.me/theorems/3fe71566-cd40-479f-8251-641b26d86cd4
-- title:
--   Weyl monotonicity: for Hermitian $0\preceq B_-\preceq B_+\preceq\Lambda$ the eigenvalues can be paired, $0\le\lambda^-_i\le\lambda^+_i\le\Lambda$
-- statement:
--   Weyl's monotonicity theorem for eigenvalues, in a form with explicit enumerations.
--
--   Let $B_-,B_+$ be Hermitian $n\times n$ complex matrices with $0\preceq B_-\preceq B_+\preceq\Lambda\mathbf 1$. Then the eigenvalues of $B_-$ and of $B_+$ can be enumerated, with multiplicity, as $\lambda^-_1,\dots,\lambda^-_n$ and $\lambda^+_1,\dots,\lambda^+_n$ so that
--
--   $$
--   0\le\lambda^-_i\le\lambda^+_i\le\Lambda\qquad\text{for every }i .
--   $$
--
--   Role. In the proof of Lemma 12 this pairs the mean photon numbers of the thermal modes of the two reduced states ("Since $B_+\ge B_-$, Weyl's monotonicity theorem yields $\lambda^+_i\ge\lambda^-_i$ for every $i$"), which is what makes the convolution coupling of the two photon-count distributions possible.
--
--   **Formalization Note** "Enumeration of the eigenvalues with multiplicity" is expressed through the consequences that are used: $\det(1+tB_\pm)=\prod_i(1+t\lambda^\pm_i)$ for all real $t$ (this determines the multiset), $\operatorname{Tr}B_\pm=\sum_i\lambda^\pm_i$ and $\operatorname{Tr}B_-^2=\sum_i(\lambda^-_i)^2$. The hypotheses are `Matrix.PosSemidef` of $B_-$, $B_+-B_-$ and $\Lambda\cdot1-B_+$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.7 (Delayed proof for Lemma 12), proof of Lemma 12, after Eq. (136) (Weyl's monotonicity theorem)

import Mathlib

open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **Weyl monotonicity: eigenvalues of Loewner-ordered Hermitian matrices can be paired.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.7, proof of Lemma 12, after Eq. (136): "Since B₊ ≥ B₋, Weyl's monotonicity theorem yields λ⁺_i ≥ λ⁻_i for every i."

Let `0 ⪯ B₋ ⪯ B₊ ⪯ Λ·1` be Hermitian `n × n` matrices. Then there are enumerations `λ⁻_1, …, λ⁻_n` and
`λ⁺_1, …, λ⁺_n` of their eigenvalues (with multiplicity) such that `0 ≤ λ⁻_i ≤ λ⁺_i ≤ Λ` for every `i`.

**Formalization Note.** "Enumeration of the eigenvalues" is expressed by the consequences that are used:
`det(1 + tB_±) = ∏ᵢ (1 + tλ^±_i)` for all real `t`, `Tr B_± = ∑ᵢ λ^±_i` and `Tr B₋² = ∑ᵢ (λ⁻_i)²`. -/
theorem loewner_eigenvalue_pairing {n : ℕ} (Bm Bp : Matrix (Fin n) (Fin n) ℂ) (hm : Bm.PosSemidef)
    (hd : (Bp - Bm).PosSemidef) (Λ : ℝ)
    (hΛ : (((Λ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Bp).PosSemidef) :
    ∃ lp lm : Fin n → ℝ, (∀ i, 0 ≤ lm i) ∧ (∀ i, lm i ≤ lp i) ∧ (∀ i, lp i ≤ Λ) ∧
      (∀ t : ℝ, (1 + ((t : ℝ) : ℂ) • Bp).det = ∏ i, ((1 + t * lp i : ℝ) : ℂ)) ∧
      (∀ t : ℝ, (1 + ((t : ℝ) : ℂ) • Bm).det = ∏ i, ((1 + t * lm i : ℝ) : ℂ)) ∧
      Bp.trace = ((∑ i, lp i : ℝ) : ℂ) ∧ Bm.trace = ((∑ i, lm i : ℝ) : ℂ) ∧
      (Bm * Bm).trace = ((∑ i, lm i ^ 2 : ℝ) : ℂ) := by sorry

end BosonicLearn
