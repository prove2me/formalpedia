-- Prove2me | Theorems.Thm_DiazModulus_params_1122_eventually
-- name    : DiazModulus.params_1122_eventually
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:50.396001+00:00
-- url     : https://prove2.me/theorems/fa8ebde9-b3cf-4212-a192-c25f8fe6294f
-- title:
--   Th. 11.21 Step 7a: with $S_0 = \lfloor S_1^\mu (\log S_1)^\nu \rfloor$, T₀ = ⌊S₀/log S₁⌋, T₁ = ⌊S₀/S₁⌋, μ = d₁/(d−n), ν > (d₀+n)/(d−n), the constraint of Steps 3–5 holds for large S₁
-- statement:
--   Let $d_0, d_1, n \in \mathbb{N}$ with $1 \leq n < d = d_0 + d_1$ and $d_0 \leq n$, let $C > 0$ and $\nu > (d_0 + n)/(d - n)$. For $S_1 \in \mathbb{N}$ put $S_0 = \lfloor S_1^{d_1/(d - n)} (\log S_1)^\nu \rfloor$, $T_0 = \lfloor S_0 / \log S_1 \rfloor$ and $T_1 = \lfloor S_0 / S_1 \rfloor$. Then for all large $S_1$: $T_0 \geq 2$, $T_1 \geq 2$, and $C(S_0 \log(T_0 + T_1 + 2) + T_0 \log(S_1 + 2) + T_1(S_1 + 1)) \leq ((T_0 + 1)^{d_0} (2T_1 + 1)^{d_1})^{1/n}$.
--
--   **Proof.** Write $x = S_1$, $\Lambda = \log x$, $e = d_1/(d - n) \geq 1$ and $F = x^e \Lambda^\nu$. As $\nu > 0$ and $e \geq 1$, $F/x \geq \Lambda^\nu \to \infty$, so the floors give $T_0 \geq F/(2\Lambda)$, $T_1 \geq F/(2x)$, both $\geq 2$, and $T_0 \leq F/\Lambda$, $T_1 \leq F/x$. The left side is at most $K F \Lambda$ with $K = C(6 + e + \nu)$, and the right side at least $((F/(2\Lambda))^{d_0} (F/x)^{d_1})^{1/n}$. Comparing logarithms, with $\log F = e\Lambda + \nu \log\Lambda$, the coefficient of $\Lambda$ is $(e(d - n) - d_1)/n = 0$ and that of $\log\Lambda$ is $((d - n)\nu - d_0 - n)/n > 0$, so the inequality holds once $\log\log x$ is large.
--
--   **Novelty.** Classical; routine formalisation. Step 7 of the proof of DALAG Th. 11.21: the parameters satisfy condition (11.22).
-- source:
--   Step 7 (choice of parameters, condition (11.22)) of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1). C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem params_1122_eventually {d0 d1 n : ℕ} (hn : 1 ≤ n) (hnd : n < d0 + d1) (hd0n : d0 ≤ n)
    (C : ℝ) (hC : 0 < C) (ν : ℝ) (hν : ((d0 : ℝ) + n) / ((d0 : ℝ) + d1 - n) < ν) :
    ∀ᶠ S₁ : ℕ in Filter.atTop,
      2 ≤ ⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ ∧
      2 ≤ ⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ ∧
      C * (((⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℕ) : ℝ) * Real.log (((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ : ℕ) : ℝ)
            + ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ : ℕ) : ℝ) + 2)
          + ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ : ℕ) : ℝ) * Real.log ((S₁ : ℝ) + 2)
          + ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ : ℕ) : ℝ) * ((S₁ : ℝ) + 1))
        ≤ ((((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊) + 1) ^ d0 * (2 * (⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊) + 1) ^ d1 : ℕ) : ℝ)
            ^ ((1 : ℝ) / n) := by
  sorry

end DiazModulus
