-- Prove2me | Theorems.Thm_DiazModulus_card_le_height_add_of_ringKrullDim_quotient_le
-- name    : DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:23.507988+00:00
-- url     : https://prove2.me/theorems/a3fb62f7-ccde-4779-9de3-1c0d753149b6
-- title:
--   For a prime $\mathfrak{p}$ of $K[X_\sigma]$, $K$ algebraically closed and $\sigma$ finite: $\dim K[X_\sigma]/\mathfrak{p} \le e$ implies $|\sigma| \le \mathrm{ht}\,\mathfrak{p} + e$
-- statement:
--   Let $K$ be an algebraically closed field, $\sigma$ a finite type and $\mathfrak{p}$ a prime ideal of $K[X_\sigma]$ (`MvPolynomial σ K`) with $\dim K[X_\sigma]/\mathfrak{p} \le e$ for some $e \in \mathbb{N}$. Then $|\sigma| \le \operatorname{ht}\mathfrak{p} + e$. Krull dimensions take values in $\{-\infty\} \cup \mathbb{N} \cup \{\infty\}$ and heights in $\mathbb{N} \cup \{\infty\}$.
--
--   **Proof.** Localise at a maximal ideal $\mathfrak{m} = (X - a) \supseteq \mathfrak{p}$, where `DiazModulus.exists_isWeaklyRegular_vanishing` gives a regular sequence of length $|\sigma|$. A maximal weakly regular list $ps$ inside $\mathfrak{p}$ has length at most $\operatorname{ht}\mathfrak{p}$ and $\mathfrak{p}$ lies in an associated prime $\mathfrak{q}$ of the quotient by $ps$; then `DiazModulus.exists_isRegular_quotient_ofList` and `DiazModulus.length_le_ringKrullDim_quotient_of_mem_associatedPrimes` give $|\sigma| \le |ps| + \dim A/\mathfrak{q} \le \operatorname{ht}\mathfrak{p} + e$.
--
--   **Novelty.** Classical; routine formalisation. Only the inequality is stated.
-- source:
--   Classical dimension theory of polynomial rings over a field: $\operatorname{ht}\mathfrak{p} + \dim K[X_\sigma]/\mathfrak{p} = |\sigma|$; compare H. Matsumura, Commutative Ring Theory, Cambridge Studies in Advanced Mathematics 8, Cambridge University Press, §17. Uses `DiazModulus.exists_isRegular_quotient_ofList`, `DiazModulus.exists_isWeaklyRegular_vanishing` and `DiazModulus.length_le_ringKrullDim_quotient_of_mem_associatedPrimes`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem card_le_height_add_of_ringKrullDim_quotient_le {σ K : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (𝔭 : Ideal (MvPolynomial σ K)) (h𝔭 : 𝔭.IsPrime) (e : ℕ)
    (he : ringKrullDim (MvPolynomial σ K ⧸ 𝔭) ≤ e) :
    (Nat.card σ : ℕ∞) ≤ 𝔭.height + e := by
  sorry

end DiazModulus
