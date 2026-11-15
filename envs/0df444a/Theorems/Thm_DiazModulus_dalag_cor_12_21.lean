-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_12_21
-- name    : DiazModulus.dalag_cor_12_21
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:45.925727+00:00
-- url     : https://prove2.me/theorems/05604f1b-d2fe-47c6-bf3c-b25f01f4afda
-- title:
--   DALAG Cor. 12.21: if a d × ℓ matrix M = (Λᵢⱼ) over ℒ̃ has Σᵢⱼ τᵢσⱼΛᵢⱼ ≠ 0 for all non-zero τ ∈ Q̄ᵈ and σ ∈ Q̄^ℓ, then dℓ ≤ rank(M)(d + ℓ)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M = (\Lambda_{ij})$ be a $d \times \ell$ matrix with entries in $\widetilde{\mathcal L}$ such that
--   $$\sum_{i=1}^d \sum_{j=1}^\ell \tau_i \sigma_j \Lambda_{ij} \ne 0$$
--   for all non-zero $\tau \in \overline{\mathbb Q}^d$ and $\sigma \in \overline{\mathbb Q}^\ell$. Then
--   $$d\,\ell \le \operatorname{rank}(M)\,(d + \ell),$$
--   that is, $\operatorname{rank}(M) \ge d\ell/(d + \ell)$ when $d + \ell > 0$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §12.3, Cor. 12.21 (p. 435), from Th. 12.20, that is D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 1 (p. 38), proved on the platform as DiazModulus.roy_rank_bound. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_12_21 {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hfree : ∀ (τ : Fin d → ℂ) (σ : Fin l → ℂ), (∀ i, τ i ∈ Qbar) → (∀ j, σ j ∈ Qbar) →
      τ ≠ 0 → σ ≠ 0 → ∑ i, ∑ j, τ i * σ j * M i j ≠ 0) :
    d * l ≤ M.rank * (d + l) := by
  sorry

end DiazModulus
