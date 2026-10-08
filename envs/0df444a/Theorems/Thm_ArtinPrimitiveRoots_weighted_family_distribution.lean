-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_weighted_family_distribution
-- name    : ArtinPrimitiveRoots.weighted_family_distribution
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:58.74254+00:00
-- url     : https://prove2.me/theorems/b87cd752-7469-4446-b2ec-63407911a5d6
-- title:
--   Lemma 12.3 (OpenAI) — distribution of the weighted family, and the size of the total mass
-- statement:
--   Let $M > 0$ with $8 \mid M$, and let $\Psi : \mathbb R \to \mathbb R$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int\Psi > 0$. Write $A_\Psi = \int_1^2 \Psi(y)\,dy$, $L = \log x$, $J_0 = $ `harmonicMass x a`, $X_0 = $ `totalMass M c u Ψ x a`, $\mathcal W = $ `mark (1/2) x a` and $E_r(\ell) = $ `massRemainder M c u Ψ x r ℓ`. Call $(c, u, K, a)$ admissible if $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$, $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$, $K \ge 1$ and $0.1 < a_1 < \cdots < a_K < 0.2$.
--
--   1. For admissible $(c, u, K, a)$, all $0 < \kappa < 0.01$, $0 < \varepsilon < \kappa$ and $A > 0$, there are $C$ and $x_0$ such that for $x \ge x_0$, with $D = x^{1/2 - \kappa/2}$,
--   $$\sum_{r \le x^\varepsilon}\mathcal W(r)\sum_{\ell \le D,\ \ell \text{ odd squarefree}} |E_r(\ell)| \le C\,x\,J_0\,L^{-A},$$
--   where $r$ runs over group integers (`IsGroupInteger x a`).
--   2. For admissible $(c, u, K, a)$ and every $\eta > 0$ there is $x_0$ such that for $x \ge x_0$,
--   $$\Bigl|X_0 - \frac{xJ_0A_\Psi}{c\,\varphi(M/c)\,L}\Bigr| \le \eta\,\frac{xJ_0A_\Psi}{c\,\varphi(M/c)\,L}.$$
--   3. There are $c_1, c_2 > 0$, depending only on $M$ and $\Psi$, such that for admissible $(c, u, K, a)$ there is $x_0$ with $c_1\,xJ_0/L \le X_0 \le c_2\,xJ_0/L$ for all $x \ge x_0$.
--
--   **Formalization note.** The standing assumptions (12.11) enter only where they occur: $\kappa$ and $\varepsilon$ through $D$ and $r \le x^\varepsilon$ in part 1; $b$ appears in none of the claims and is omitted. Part 2 writes $X_0 \sim xJ_0A_\Psi/(c\varphi(M/c)L)$ as a relative error at most $\eta$ for large $x$. In part 3, $\asymp_{M,\Psi}$ is taken literally: $c_1, c_2$ are chosen before $c$, $u$, $K$ and the $a_i$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 77: “Take temporarily $0 < \kappa < 0.01$, $0 < \varepsilon < \kappa$, $0 < b < 0.01$, $D = x^{1/2-\kappa/2}$. (12.11) … Lemma 12.3 (Distribution of the weighted family). For every fixed $A > 0$, $\sum_{r \le x^\varepsilon}\mathcal W(r)\sum_{\ell \le D,\ \ell \text{ odd squarefree}}|E_r(\ell)| \ll xJ_0L^{-A}$. (12.13) Moreover, writing $A_\Psi = \int_1^2\Psi(y)\,dy$, we have $X_0 \sim \frac{xJ_0A_\Psi}{c\varphi(M/c)L}$ $(x \to \infty)$, (12.14) with all construction parameters fixed and $J_0 = J_0(x)$. In particular, $X_0 \asymp_{M,\Psi} \frac{xJ_0}{L}$, (12.15) with comparison constants independent of $K, \kappa, \varepsilon, b$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, Lemma 12.3

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem weighted_family_distribution (M : ℕ) (hM : 0 < M) (h8 : 8 ∣ M)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    (∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      (∀ κ ε : ℝ, 0 < κ → κ < 0.01 → 0 < ε → ε < κ →
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
          ∑ r ∈ (Finset.range (⌊x ^ ε⌋₊ + 1)).filter (IsGroupInteger x a),
              mark (1 / 2) x a r *
                ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter
                    (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
                  |massRemainder M c u Ψ x r ℓ| ≤
            C * (x * harmonicMass x a * log x ^ (-A))) ∧
      (∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        |totalMass M c u Ψ x a -
            x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)| ≤
          η * (x * harmonicMass x a * (∫ y in (1 : ℝ)..2, Ψ y) /
              (c * Nat.totient (M / c) * log x)))) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        c₁ * (x * harmonicMass x a / log x) ≤ totalMass M c u Ψ x a ∧
          totalMass M c u Ψ x a ≤ c₂ * (x * harmonicMass x a / log x) := by
  sorry

end ArtinPrimitiveRoots
