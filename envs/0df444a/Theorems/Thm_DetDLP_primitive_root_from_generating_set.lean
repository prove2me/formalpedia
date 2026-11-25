-- Prove2me | Theorems.Thm_DetDLP_primitive_root_from_generating_set
-- name    : DetDLP.primitive_root_from_generating_set
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:49:34.211955+00:00
-- url     : https://prove2.me/theorems/047d5ba6-bf88-49d5-907b-4fcdc83f3f61
-- title:
--   Primitive Root Construction from a $2m$-Covering Factor Base of $\mathbb{F}_p^*$
-- statement:
--   Let $p$ be a prime and let $F_1, \dots, F_m \subseteq \mathbb{F}_p^*$ be lists whose $2m$-fold product set covers $\mathbb{F}_p^*$. Then:
--   1. For every prime divisor $\pi \mid (p - 1)$, there exist $i$ and $a \in F_i$ with $a^{(p - 1)/\pi} \not\equiv 1 \pmod p$.
--   2. For any choice of witnesses $a_\pi \in \mathbb{F}_p^*$ satisfying $a_\pi^{(p - 1)/\pi} \neq 1$ for each prime $\pi \mid (p - 1)$, the product $h = \prod_{\pi \mid (p-1)} a_\pi^{(p-1)/\pi^{v_\pi(p-1)}}$ has exact order $p - 1$ (i.e., $h$ is a primitive root modulo $p$).
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.3, Proof of Proposition 3.3 (p. 14)

import Mathlib

set_option autoImplicit false

namespace DetDLP

/-- Algebraic core of Proposition 3.3 (Section 3.3): given any prime `p` and any family of
factor-base lists `F : Fin m → List (ZMod p)ˣ` whose 2m-fold products cover `(ZMod p)ˣ`,
for every prime divisor `π` of `p - 1` there exists an element `a_π` in the union of `F i`
with `a_π ^ ((p - 1) / π) ≠ 1`; moreover, for ANY such choice `a`, the product
`h = ∏ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)`
is a primitive root modulo `p` (`orderOf h = p - 1`). -/
theorem primitive_root_from_generating_set :
    ∀ (p m : ℕ) [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ),
      (∀ X : (ZMod p)ˣ, ∃ A B : Fin m → (ZMod p)ˣ,
        (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
        (∏ i : Fin m, (A i * B i)) = X) →
      (∀ π ∈ (p - 1).primeFactors,
        ∃ i : Fin m, ∃ a ∈ F i, a ^ ((p - 1) / π) ≠ 1) ∧
      (∀ a : ℕ → (ZMod p)ˣ,
        (∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1) →
        orderOf (∏ π ∈ (p - 1).primeFactors,
          (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)) = p - 1) := by sorry

end DetDLP
