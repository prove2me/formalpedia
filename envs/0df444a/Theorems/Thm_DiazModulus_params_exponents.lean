-- Prove2me | Theorems.Thm_DiazModulus_params_exponents
-- name    : DiazModulus.params_exponents
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:49.957995+00:00
-- url     : https://prove2.me/theorems/2de60bd7-dc9d-48ef-909e-5d1905d00cd5
-- title:
--   Th. 11.21 Step 7b: if (11.23) holds with exponents (ℓ₀′, λ′, d₀′, d₁′) for infinitely many S₁, then ℓ₀′ < d′ and (λ′ + d₁′)(d − n) ≤ d₁(d′ − ℓ₀′)
-- statement:
--   Let $d_0, d_1, n \in \mathbb{N}$ with $n < d = d_0 + d_1$ and $d_0 \leq n$, let $\nu > 0$, $c_8 \in \mathbb{R}$, and $a, b, c_0, c_1 \in \mathbb{N}$ with $c_0 + c_1 \geq 1$ and $a \leq c_0 + c_1$. For $S_1 \in \mathbb{N}$ put $S_0 = \lfloor S_1^{d_1/(d - n)} (\log S_1)^\nu \rfloor$, $T_0 = \lfloor S_0 / \log S_1 \rfloor$ and $T_1 = \lfloor S_0 / S_1 \rfloor$. Suppose that for infinitely many $S_1$, $\lfloor S_0/d \rfloor^a \lfloor S_1/d \rfloor^b \leq c_8 T_0^{c_0} T_1^{c_1}$ (an inequality of the shape (11.23)). Then $a < c_0 + c_1$ and $(b + c_1)(d - n) \leq d_1(c_0 + c_1 - a)$.
--
--   **Proof.** With $x = S_1$, $\Lambda = \log x$, $e = d_1/(d - n)$ and $F = x^e\Lambda^\nu$, for large $x$ the left side is at least $(F/(2d))^a (x/(2d))^b$ and the right side at most $\max(c_8, 1) (F/\Lambda)^{c_0} (F/x)^{c_1}$. The logarithm of their ratio is $-g\Lambda - h\log\Lambda - \mathrm{const}$ with $g = e(c_0 + c_1 - a) - c_1 - b$ and $h = \nu(c_0 + c_1 - a) - c_0$. If the conclusion fails, then $g < 0$, or $g = 0$ and $h = -c_0 < 0$ (when $a = c_0 + c_1$ and $b = c_1 = 0$). In both cases the left side exceeds the right side for all large $S_1$, against the hypothesis.
--
--   **Novelty.** Classical; routine formalisation. Step 7 of the proof of DALAG Th. 11.21: the exponents of (11.23).
-- source:
--   Step 7 (from (11.23) to the conclusion) of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1). C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem params_exponents {d0 d1 n : ℕ} (hnd : n < d0 + d1) (hd0n : d0 ≤ n)
    (ν : ℝ) (hν0 : 0 < ν) (c8 : ℝ) (a b c0 c1 : ℕ) (hd' : 1 ≤ c0 + c1) (ha : a ≤ c0 + c1)
    (hfreq : ∃ᶠ S₁ : ℕ in Filter.atTop,
      ((⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ / (d0 + d1) : ℕ) : ℝ) ^ a *
          ((S₁ / (d0 + d1) : ℕ) : ℝ) ^ b
        ≤ c8 * ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ : ℕ) : ℝ) ^ c0 * ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ : ℕ) : ℝ) ^ c1) :
    a < c0 + c1 ∧ (b + c1) * (d0 + d1 - n) ≤ d1 * (c0 + c1 - a) := by
  sorry

end DiazModulus
