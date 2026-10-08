-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
-- name    : ArtinPrimitiveRoots.harmonic_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:28:23.991854+00:00
-- url     : https://prove2.me/theorems/d54e39c8-fb70-478a-bcd6-a64accaea7ed
-- title:
--   Lemma 12.2 (OpenAI) — harmonic mass: Euler product, bounds and tail
-- statement:
--   Let $M, c, u$ satisfy (12.1) and let $\Psi$ be as in §12 ($C^\infty$, closed support in $(1, 2)$, $0 \le \Psi \le 1$, $\int\Psi > 0$), and let $K \ge 1$. There is $C$ such that for all band exponents $0.1 < a_1 < \cdots < a_K < 0.2$ and every $\varepsilon > 0$ there is $x_0$ such that for every $x \ge x_0$, with $L = \log x$, $J_0 = $ `harmonicMass x a`, $V_i = $ `groupReciprocalSum x (a i)`, $E_i(t) = \prod_{p \in \mathcal P_i}\bigl(1 + \frac{t}{p-1}\bigr)$, $\mathcal W = $ `mark (1/2) x a`, and $r$ running over group integers (`IsGroupInteger x a`):
--
--   1. $J_0 = \prod_{i=1}^K E_i'(1/2)/V_i$, where $E_i'$ is the derivative of the finite product;
--   2. $J_0 = \prod_{i=1}^K \Bigl\{\frac{E_i(1/2)}{V_i}\sum_{p \in \mathcal P_i}\frac{1}{p - 1 + 1/2}\Bigr\}$;
--   3. $1 \le J_0 \le C$;
--   4. $\sum_{r > x^\varepsilon} \mathcal W(r)/r \le C\exp(-\varepsilon L^{1 - a_K})$;
--   5. $\sum_{r > x^\varepsilon} \mathcal W(r)\,A_r \le C\,x\exp(-\varepsilon L^{1 - a_K})$, where $A_r = $ `predecessorMass M c u Ψ x r`.
--
--   $C$ depends only on $M, c, u, \Psi$ and $K$, not on the $a_i$ or $\varepsilon$; $x_0$ may depend on everything.
--
--   **Formalization note.** The subscript in $\ll_K$ is taken literally: the constant $C$ is chosen before the band exponents and $\varepsilon$. “The part of $X_0$ with $r > x^\varepsilon$” is $\sum_{r > x^\varepsilon}\mathcal W(r)A_r$, following the expression $X_0 = \sum_r \mathcal W(r)A_r$ in (12.8). The identities are claimed only for $x \ge x_0$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 76: “Lemma 12.2 (Harmonic mass). For each group put $E_i(t) = \prod_{p \in \mathcal P_i}\bigl(1 + \frac{t}{p-1}\bigr)$. The harmonic mass has the exact Euler-product expression $J_0 = \prod_{i=1}^K \frac{E_i'(1/2)}{V_i} = \prod_{i=1}^K\Bigl\{\frac{E_i(1/2)}{V_i}\sum_{p \in \mathcal P_i}\frac{1}{p - 1 + 1/2}\Bigr\}$. (12.9) For every fixed $\varepsilon > 0$, $1 \le J_0 \ll_K 1$, $\sum_{r > x^\varepsilon}\frac{\mathcal W(r)}{r} \ll_K \exp(-\varepsilon L^{1-a_K})$. (12.10) Consequently the part of $X_0$ with $r > x^\varepsilon$ is $O_K(x\exp(-\varepsilon L^{1-a_K}))$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 76, Lemma 12.2

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem harmonic_mass (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        harmonicMass x a =
          ∏ i, deriv (fun t : ℝ => ∏ p ∈ primeGroup x (a i), (1 + t / ((p : ℝ) - 1))) (1 / 2) /
            groupReciprocalSum x (a i) ∧
        harmonicMass x a =
          ∏ i, ((∏ p ∈ primeGroup x (a i), (1 + (1 / 2) / ((p : ℝ) - 1))) /
              groupReciprocalSum x (a i) *
            ∑ p ∈ primeGroup x (a i), 1 / ((p : ℝ) - 1 + 1 / 2)) ∧
        1 ≤ harmonicMass x a ∧ harmonicMass x a ≤ C ∧
        ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r}, mark (1 / 2) x a r / (r : ℝ) ≤
          C * exp (-ε * log x ^ (1 - a ⟨K - 1, by omega⟩)) ∧
        ∑' r : {r : ℕ // IsGroupInteger x a r ∧ x ^ ε < r},
            mark (1 / 2) x a r * predecessorMass M c u Ψ x r ≤
          C * (x * exp (-ε * log x ^ (1 - a ⟨K - 1, by omega⟩))) := by
  sorry

end ArtinPrimitiveRoots
