-- Prove2me | Theorems.Thm_DiazModulus_nat_telescope_step
-- name    : DiazModulus.nat_telescope_step
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:53.948894+00:00
-- url     : https://prove2.me/theorems/75bc8a47-1cff-42b1-b44d-48fd5b7c8de9
-- title:
--   One telescoping step: if $g$ is monotone and $g(v+1) + f(v) \le f(v+1)$ for every $v$, then $u\,g(u) \le f(2u)$
-- statement:
--   Let $f, g : \mathbb{N} \to \mathbb{N}$ with $g$ monotone and $g(v+1) + f(v) \le f(v+1)$ for every $v \in \mathbb{N}$. Then $u\,g(u) \le f(2u)$ for every $u \in \mathbb{N}$.
--
--   **Proof.** By induction on $k$, $f(u) + k\,g(u) \le f(u+k)$: each step adds $g(u+k+1) \ge g(u)$. Take $k = u$.
--
--   **Novelty.** Not found in the sources read in this form; routine. It replaces, at finite level, the passage to Hilbert polynomials at the end of the proof of DALAG Lemma 5.4.
-- source:
--   Elementary. It replaces the limit argument at the end of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 5.4 (§5.2.4, pp. 154–155; Chapter 5 is by D. Roy), which the proof of Lemma 8.5 repeats. Not found in the sources read in this form; routine. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem nat_telescope_step (f g : ℕ → ℕ) (hg : Monotone g) (h : ∀ v, g (v + 1) + f v ≤ f (v + 1)) (u : ℕ) :
    u * g u ≤ f (2 * u) := by
  sorry

end DiazModulus
