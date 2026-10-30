-- Prove2me | Theorems.Thm_DiazModulus_thetaN_ge_mul_sub
-- name    : DiazModulus.thetaN_ge_mul_sub
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:35.266991+00:00
-- url     : https://prove2.me/theorems/daa369ed-f5d2-4cdc-ac1e-bbaea498db12
-- title:
--   Θₙ(L), the least total degree of L distinct multi-indices in ℕⁿ, is at least A·(L − Aⁿ) for every A
-- statement:
--   Let $n \geq 1$ and $L, A \in \mathbb{N}$. Then $A\,(L - A^n) \leq \Theta_n(L)$, where $\Theta_n(L)$ is the least value of $\sum_l |\kappa'(l)|$ over the injective maps $\kappa' : \{1, \dots, L\} \to \mathbb{N}^n$, with $|\cdot|$ the total degree of a multi-index ($0$ if there is no such map), and $L - A^n$ is truncated at $0$.
--
--   **Proof.** For $n \geq 1$ the map $l \mapsto (l, \dots, l)$ is injective, so it suffices to bound every admissible sum from below. Fix an injective $\kappa'$. At most $A^n$ indices $l$ have $\kappa'(l)$ in the box $\{0, \dots, A - 1\}^n$, as $\kappa'$ maps them injectively into it; every other $l$ has a coordinate $\geq A$, hence degree $\geq A$. So the total degree is at least $A$ times the number of indices outside the box, which is at least $L - A^n$.
--
--   **Novelty.** Not found in the sources read in this form; routine. An elementary lower bound for $\Theta_n(L)$ (DALAG §6.2.2), enough here in place of the sharper DALAG Lemma 6.5 (§6.2.3).
-- source:
--   The function Θₙ(L) is that of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §6.2.2; compare Lemma 6.5 (§6.2.3) there. Not found in the sources read in this form; routine. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem thetaN_ge_mul_sub (n L A : ℕ) (hn : 1 ≤ n) :
    A * (L - A ^ n) ≤ sInf {S | ∃ κ' : Fin (L) → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} := by
  sorry

end DiazModulus
