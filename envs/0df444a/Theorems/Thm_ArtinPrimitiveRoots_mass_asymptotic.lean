-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_mass_asymptotic
-- name    : ArtinPrimitiveRoots.mass_asymptotic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T14:11:40.307332+00:00
-- url     : https://prove2.me/theorems/da8bc65b-a480-444f-aa10-cae78db75b04
-- title:
--   Proof of Lemma 12.3 (OpenAI), (12.14) — the asymptotic for the total mass
-- statement:
--   Let $M, c, u$ satisfy (12.1): $M > 0$, $8 \mid M$, $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$ and $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$. Let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int\Psi > 0$, and write $A_\Psi = \int_1^2\Psi(y)\,dy$ and $L = \log x$. Let $K \ge 1$ and $0.1 < a_1 < \cdots < a_K < 0.2$. Then for every $\eta > 0$ there is $x_0$ such that for every $x \ge x_0$,
--
--   $$\Bigl|X_0 - \frac{xJ_0A_\Psi}{c\,\varphi(M/c)\,L}\Bigr| \;\le\; \eta\,\frac{xJ_0A_\Psi}{c\,\varphi(M/c)\,L}.$$
--
--   Here $X_0 = $ `totalMass M c u Ψ x a` and $J_0 = $ `harmonicMass x a`.
--
--   **Formalization note.** $X_0 \sim xJ_0A_\Psi/(c\varphi(M/c)L)$ is written as a relative error at most $\eta$ for large $x$; this is part 2 of the published Lemma 12.3.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 78–79: “To obtain the precise asymptotic, fix an auxiliary exponent $0 < \theta < \varepsilon$, without changing the sieve parameters. […] Use the $\ell = 1$ term of (12.18) with $A' > 2$, multiply by $\mathcal W(r)$, and sum over $r \le x^\theta$. The summed progression error is $O(xJ_0L^{-A'})$. Lemma 12.2 bounds the omitted parts of both $X_0$ and $J_0$; after the harmonic tail is multiplied by $x/L$, both are $o_\theta(xJ_0/L)$, since $J_0 \ge 1$. Thus $\frac{c\varphi(N)LX_0}{xJ_0A_\Psi} = 1 + O(\theta) + o_\theta(1)$. First let $x$ tend to infinity with $\theta$ fixed, and then let $\theta$ decrease to zero. This proves (12.14).”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 78–79, proof of Lemma 12.3, (12.14)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem mass_asymptotic (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (hΨi : 0 < ∫ y, Ψ y) (K : ℕ) (hK : 1 ≤ K) (a : Fin K → ℝ) (ha : StrictMono a)
    (hai : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) (η : ℝ) (hη : 0 < η) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |totalMass M c u Ψ x a -
          x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) / (c * Nat.totient (M / c) * log x)| ≤
        η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
          (c * Nat.totient (M / c) * log x)) := by
  sorry

end ArtinPrimitiveRoots
