-- Prove2me | Theorems.Thm_DeepSets_exists_rho_of_four_pow_code
-- name    : DeepSets.exists_rho_of_four_pow_code
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:49:34.718149+00:00
-- url     : https://prove2.me/theorems/505d7c14-eeae-460d-8b1b-245305fe3bf3
-- title:
--   Proof of Theorem 2 — construction of $\rho:\mathbb R\to\mathbb R$ with $f(X)=\rho\left(\sum_{x\in X}4^{-c(x)}\right)$
-- statement:
--   Let $U$ be a set of elements and $c : U\to\mathbb N$ injective, and put $\phi(x)=4^{-c(x)}$. For every real-valued function $f$ of the finite subsets of $U$ there is a function $\rho:\mathbb R\to\mathbb R$ such that
--   $$
--   f(X) = \rho\Bigl(\sum_{x\in X}4^{-c(x)}\Bigr)\qquad\text{for every finite } X\subseteq U.
--   $$
--   This is the last step of the necessity half of Theorem 2: once the sum encodes the set, the set function is a function of the sum.
--
--   **Formalization Note** The set function is $g:\mathrm{Finset}\,U\to\mathbb R$. The countability of the elements enters through the injective $c$, as in the proof; Mathlib's `Countable.exists_injective_nat` gives one for every countable $U$.
--
--   Differences from the source:
--   - reading: "a mapping from the elements to natural numbers" c : 𝔛 → ℕ → an injective c : U → ℕ; reason: the step relies on the unique representation of the previous sentence, which forces injectivity; a countable set has such a map
--   - reading: the set function f on 2^𝔛 → g : Finset U → ℝ; reason: in §A the elements of 2^𝔛 on which f acts are the sets X = {x₁, …, x_M}, so 2^𝔛 denotes finite sets there
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12 (PDF p.12), "Now a function ρ : ℝ → ℝ can always be constructed such that f(X) = ρ(Σ_{x∈X} φ(x))"

import Mathlib

namespace DeepSets

/-- Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12,
"Now a function `ρ : ℝ → ℝ` can always be constructed such that `f(X) = ρ(∑_{x∈X} φ(x))`",
where `φ(x) = 4^{-c(x)}` for the mapping `c : 𝔛 → ℕ` introduced just before.

For an injective `c : U → ℕ` and every real function `g` of finite subsets of `U`, there is
`ρ : ℝ → ℝ` with `g(X) = ρ(∑_{x ∈ X} 4^{-c(x)})` for every finite `X ⊆ U`.

**Formalization Note** The set function `f(X)` of the page is `g : Finset U → ℝ` (the sets of §A
are finite). The countability of the elements enters, as in the proof, through the injective
`c : U → ℕ`; Mathlib's `Countable.exists_injective_nat` provides one for any countable `U`. -/
theorem exists_rho_of_four_pow_code {U : Type*} (c : U → ℕ) (hc : Function.Injective c)
    (g : Finset U → ℝ) :
    ∃ ρ : ℝ → ℝ, ∀ X : Finset U, g X = ρ (∑ x ∈ X, (4 : ℝ) ^ (-(c x : ℤ))) := by sorry

end DeepSets
