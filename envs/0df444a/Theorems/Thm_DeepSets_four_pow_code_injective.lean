-- Prove2me | Theorems.Thm_DeepSets_four_pow_code_injective
-- name    : DeepSets.four_pow_code_injective
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:32.761658+00:00
-- url     : https://prove2.me/theorems/78e9ab0d-725a-46cb-acf8-e2c811df9bce
-- title:
--   Proof of Theorem 2 — $\sum_{x\in X}4^{-c(x)}$ is a unique representation of the finite set $X$
-- statement:
--   Let $U$ be a set of elements and $c : U\to\mathbb N$ an injective map (an enumeration of the elements by natural numbers). Put $\phi(x)=4^{-c(x)}$. Then distinct finite subsets of $U$ have distinct sums: for finite $X,Y\subseteq U$,
--   $$
--   \sum_{x\in X}4^{-c(x)} = \sum_{y\in Y}4^{-c(y)} \quad\Longrightarrow\quad X=Y .
--   $$
--   So $\sum_{x\in X}\phi(x)$ is a real number that encodes the set $X$; this is the step of the necessity proof of Theorem 2 that turns a set function into a function of one real variable.
--
--   **Formalization Note** $4^{-c(x)}$ is the integer power `(4 : ℝ) ^ (-(c x : ℤ))`.
--
--   Differences from the source:
--   - reading: "a mapping from the elements to natural numbers" c : 𝔛 → ℕ → an injective c : U → ℕ; reason: "unique representation" forces injectivity (a non-injective c gives {x} and {y} with c x = c y the same sum); a countable set has such a map
--   - reading: every set X ∈ 2^𝔛 → every finite X : Finset U; reason: in §A the elements of 2^𝔛 on which f acts are the sets X = {x₁, …, x_M}, so 2^𝔛 denotes finite sets there
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12 (PDF p.12), "To prove necessity … Now if we let φ(x) = 4^{−c(x)} then Σ_{x∈X} φ(x) constitutes an unique representation for every set X ∈ 2^𝔛"

import Mathlib

namespace DeepSets

/-- Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12,
"Let this mapping be denoted by `c : 𝔛 → ℕ`. Now if we let `φ(x) = 4^{-c(x)}` then
`∑_{x∈X} φ(x)` constitutes an unique representation for every set `X ∈ 2^𝔛`."

For an injective `c : U → ℕ`, the map `X ↦ ∑_{x ∈ X} 4^{-c(x)}` is injective on finite subsets
`X` of `U`: distinct sets get distinct sums.

**Formalization Note** The "mapping from the elements to natural numbers" is taken injective,
as "unique representation" forces (a non-injective `c` sends `{x}` and `{y}` with
`c x = c y` to the same sum). The sets `X ∈ 2^𝔛` are the finite sets `{x₁, …, x_M}` on which
`f` is defined in §A, so `X : Finset U`. The power `4^{-c(x)}` is the integer power
`(4 : ℝ) ^ (-(c x : ℤ))`. -/
theorem four_pow_code_injective {U : Type*} (c : U → ℕ) (hc : Function.Injective c) :
    Function.Injective (fun X : Finset U => ∑ x ∈ X, (4 : ℝ) ^ (-(c x : ℤ))) := by sorry

end DeepSets
