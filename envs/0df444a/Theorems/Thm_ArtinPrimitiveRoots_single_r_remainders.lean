-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_single_r_remainders
-- name    : ArtinPrimitiveRoots.single_r_remainders
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T14:12:39.925983+00:00
-- url     : https://prove2.me/theorems/564c94c0-b35e-4358-b298-bb3881c83cb4
-- title:
--   Proof of Lemma 12.3 (OpenAI), p. 78 — the remainders for a single group integer r
-- statement:
--   Let $M, c, u$ satisfy (12.1): $M > 0$, $8 \mid M$, $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$ and $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$. Let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$ and $0 \le \Psi \le 1$. Let $0 < \kappa < 0.01$, $0 < \varepsilon < \kappa$ and $A > 0$. Then there are $C \ge 0$ and $x_0$ such that for every $x \ge x_0$ and every $r \ge 1$ with $r \le x^\varepsilon$ and $(r, M) = 1$,
--
--   $$\sum_{\substack{\ell \le D\\ \ell \text{ odd squarefree}}} |E_r(\ell)| \;\le\; C\,\frac xr\,L^{-A},\qquad D = x^{1/2-\kappa/2},\ L = \log x.$$
--
--   Here $E_r(\ell) = A_r(\ell) - g_r(\ell)A_r$ is `massRemainder M c u Ψ x r ℓ`, with $A_r(\ell) = $ `predecessorMassDvd M c u Ψ x r ℓ`, $A_r = A_r(1)$ and $g_r(\ell) = 1_{(\ell, Mr) = 1}/\varphi(\ell)$, as in (12.12). The sum runs over $\ell \le \lfloor D\rfloor$.
--
--   **Formalization note.** The paper states this for the $r$ in the sum (12.13), group integers $r \le x^\varepsilon$; the statement here asks only $(r, M) = 1$, which every large group integer satisfies. $C$ and $x_0$ do not depend on $r$, as "uniformly for $r \le x^\varepsilon$" requires. Of the standing assumptions (12.11), $b$ does not occur and is omitted.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 78: “The term $\ell = 1$ of (12.18) evaluates $A_r$. Replacing $I_r/\varphi(N)$ by $A_r$ in the other terms costs at most one logarithmic factor, because $\sum_{\ell \le D} g_r(\ell) \le \sum_{\ell \le D}\frac1{\varphi(\ell)} \ll L$. For example, expand $n/\varphi(n) = \sum_{d \mid n}\mu^2(d)/\varphi(d)$ and use $\sum_d \mu^2(d)/(d\varphi(d)) < \infty$. Choosing $A'$ sufficiently large gives $\sum_{\ell \le D}|E_r(\ell)| \ll (x/r)L^{-A}$; summing with the marks proves (12.13).”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 78, proof of Lemma 12.3, the remainders for a single r

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem single_r_remainders (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (κ ε A : ℝ) (hκ : 0 < κ) (hκ1 : κ < 0.01) (hε : 0 < ε) (hεκ : ε < κ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ x ^ ε → Nat.Coprime r M →
      ∑ ℓ ∈ (Finset.range (⌊x ^ (1 / 2 - κ / 2)⌋₊ + 1)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          |massRemainder M c u Ψ x r ℓ| ≤ C * (x / r * log x ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
