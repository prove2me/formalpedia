-- Prove2me | Theorems.Thm_DiazModulus_nat_telescope_iter
-- name    : DiazModulus.nat_telescope_iter
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:52.42698+00:00
-- url     : https://prove2.me/theorems/f8e206c7-8264-41ca-8198-56f825b45feb
-- title:
--   Iterated telescoping: if $f_{k+1}(v+1) + f_k(v) \le f_k(v+1)$ with $f_{k+1}$ monotone for $k < j$, then $2^{j(j-1)/2} u^j f_j(u) \le f_0(2^j u)$
-- statement:
--   Let $f_0, f_1, f_2, \dots$ be functions $\mathbb{N} \to \mathbb{N}$ and $j \in \mathbb{N}$. Assume that for every $k < j$ the function $f_{k+1}$ is monotone and $f_{k+1}(v+1) + f_k(v) \le f_k(v+1)$ for every $v \in \mathbb{N}$. Then $2^{j(j-1)/2} u^j f_j(u) \le f_0(2^j u)$ for every $u \in \mathbb{N}$ (the exponent $j(j-1)/2$ is an integer, and $0$ for $j = 0$).
--
--   **Proof.** Induction on $j$, for all $u$ at once; for $j = 0$ both sides are $f_0(u)$. For $j + 1$, `DiazModulus.nat_telescope_step` with $f = f_j$, $g = f_{j+1}$ gives $u\,f_{j+1}(u) \le f_j(2u)$, and the induction hypothesis at $2u$ gives $2^{j(j-1)/2} (2u)^j f_j(2u) \le f_0(2^{j+1} u)$. Multiply the step by $2^{j(j-1)/2} 2^j u^j$ and use $j(j-1)/2 + j = (j+1)j/2$.
--
--   **Novelty.** Not found in the sources read in this form; routine. An iterated form of the previous step, used for chains of regular elements.
-- source:
--   Elementary. A finite-level replacement for the limits in the proofs of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 5.4 (§5.2.4; Chapter 5 is by D. Roy) and Th. 8.4 (§8.2.3, pp. 236–238; Chapter 8 is by D. Roy). Not found in the sources read in this form; routine. Uses DiazModulus.nat_telescope_step. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem nat_telescope_iter (f : ℕ → ℕ → ℕ) (j : ℕ) (hmono : ∀ k < j, Monotone (f (k + 1)))
    (h : ∀ k < j, ∀ v, f (k + 1) (v + 1) + f k v ≤ f k (v + 1)) (u : ℕ) :
    2 ^ (j * (j - 1) / 2) * u ^ j * f j u ≤ f 0 (2 ^ j * u) := by
  sorry

end DiazModulus
