-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_single_r_mass
-- name    : ArtinPrimitiveRoots.single_r_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T14:11:14.697977+00:00
-- url     : https://prove2.me/theorems/1c3be089-bfb5-4d6c-8095-e2acf00f0478
-- title:
--   Proof of Lemma 12.3 (OpenAI), (12.17) — the predecessor mass of a single small r
-- statement:
--   Let $M, c, u$ satisfy (12.1): $M > 0$, $8 \mid M$, $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$ and $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$. Let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$ and $0 \le \Psi \le 1$, and write $A_\Psi = \int_1^2\Psi(y)\,dy$, $N = M/c$ and $L = \log x$. Let $0 < \theta \le 0.01$. Then there are $C \ge 0$ and $x_0$ such that for every $x \ge x_0$ and every $r \ge 1$ with $r \le x^\theta$ and $(r, M) = 1$, we have $(1 - \theta)L > 3$ and
--
--   $$\frac{x A_\Psi}{c r\,\varphi(N)\,L} - C\,\frac{x}{rL^2} \;\le\; A_r \;\le\; \frac{x A_\Psi}{c r\,\varphi(N)\,((1-\theta)L - 3)} + C\,\frac{x}{rL^2}.$$
--
--   Here $A_r = $ `predecessorMass M c u Ψ x r`: the sum of $\Psi((crQ + 1)/x)$ over primes $Q > x^{0.9}$ with $crQ + 1 \equiv u \pmod M$.
--
--   **Formalization note.** The paper's (12.17), $A_r = I_r/\varphi(N) + O((x/r)L^{-A})$, together with its evaluation $I_r = \frac{xA_\Psi}{crL}(1 + O(\theta) + O(L^{-1}))$, is stated here in the one form the proof of (12.14) uses: two-sided bounds with the logarithm in $I_r$ replaced by its extreme values $L$ and $(1-\theta)L - 3$ on the support, and the progression error taken with $A = 2$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 78: “Define $I_r = \frac{x}{cr}\int_1^2\frac{\Psi(y)}{\log((xy-1)/(cr))}\,dy$. For every fixed $0 < \theta < 0.1$, the support of $\Psi$ forces $Q > x^{0.9}$ whenever $r \le x^\theta$. The prime number theorem in the fixed reduced progressions modulo $N$, followed by partial summation, therefore gives, for every fixed $A > 0$, $A_r = \frac{I_r}{\varphi(N)} + O_{A,M,\Psi}((x/r)L^{-A})$ $(r \le x^\theta)$. (12.17) […] Uniformly for $r \le x^\theta$ and $y$ in the support of $\Psi$, $\log((xy-1)/(cr)) = L + O(\theta L + 1)$, and hence $I_r = \frac{xA_\Psi}{crL}(1 + O(\theta) + O(L^{-1}))$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 78, proof of Lemma 12.3, (12.17)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem single_r_mass (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.01) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ x ^ θ → Nat.Coprime r M →
      3 < (1 - θ) * log x ∧
      x / (c * r) * (∫ y in (1 : ℝ)..2, Ψ y) / (Nat.totient (M / c) * log x) -
          C * (x / r / log x ^ 2) ≤ predecessorMass M c u Ψ x r ∧
      predecessorMass M c u Ψ x r ≤
        x / (c * r) * (∫ y in (1 : ℝ)..2, Ψ y) / (Nat.totient (M / c) * ((1 - θ) * log x - 3)) +
          C * (x / r / log x ^ 2) := by
  sorry

end ArtinPrimitiveRoots
