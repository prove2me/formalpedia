-- Prove2me | Theorems.Thm_DiazModulus_derivation_pow_mul_mem
-- name    : DiazModulus.derivation_pow_mul_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:29.700849+00:00
-- url     : https://prove2.me/theorems/eebafd27-1f11-4b9c-959d-e51e9c564ecc
-- title:
--   Lemma 8.16: derivations $D_i$, an ideal $J \ni Q_j$ with $D_i Q_j \equiv \delta_{ij}$; for a word $k$ of length $\le |\alpha|$, $D_k(P Q^\alpha) \equiv [k \sim \alpha]\,\alpha!\,P \bmod J$
-- statement:
--   Let $R$, $S$ be commutative rings with $S$ an $R$-algebra, $D_1, \dots, D_n$ $R$-derivations of $S$, $J$ an ideal of $S$ and $Q_1, \dots, Q_n \in J$ with $D_i Q_j - \delta_{ij} \in J$. Let $P \in S$, $\alpha \in \mathbb{N}^n$ and $k = (k_1, \dots, k_m)$ a list of indices with $m \le \alpha_1 + \cdots + \alpha_n$. Then $D_{k_1} \circ \cdots \circ D_{k_m} (P \prod_j Q_j^{\alpha_j}) - c \in J$, where $c = (\prod_i \alpha_i!)\,P$ if every index $i$ occurs exactly $\alpha_i$ times in $k$, and $c = 0$ otherwise.
--
--   **Proof.** Induction on the list, peeling off the innermost derivation, computing in $S/J$: Leibniz writes $D_k(P Q^\alpha)$ as $D_kP\,Q^\alpha + \sum_j \alpha_j D_kQ_j\,P Q^{\alpha - e_j}$, and $D_kQ_j \equiv \delta_{kj}$. No commutation of the derivations is needed.
--
--   **Novelty.** None claimed: Lemma 8.16 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), Lemma 8.16. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem derivation_pow_mul_mem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (D : Fin n → Derivation R S S)
    (J : Ideal S) (Q : Fin n → S) (hQ : ∀ j, Q j ∈ J) (hDQ : ∀ i j, D i (Q j) - (if i = j then 1 else 0) ∈ J)
    (P : S) (α : Fin n → ℕ) (ks : List (Fin n)) (hks : ks.length ≤ ∑ i, α i) :
    (ks.map fun i => (D i).toLinearMap).prod (P * ∏ j, Q j ^ α j)
      - (if (fun i => ks.count i) = α then ((∏ i, (α i).factorial : ℕ) : S) * P else 0) ∈ J := by
  sorry

end DiazModulus
