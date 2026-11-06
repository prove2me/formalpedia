-- Prove2me | Theorems.Thm_DeepSets_sum_decomposition_isPermInvariant
-- name    : DeepSets.sum_decomposition_isPermInvariant
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:50:15.461195+00:00
-- url     : https://prove2.me/theorems/2b684da6-63e4-45af-abdc-025c8cccfd35
-- title:
--   Proof of Theorem 2 — sufficiency, $\rho\left(\sum_{x\in X}\phi(x)\right)$ is permutation invariant
-- statement:
--   Let $U$ be any set of elements, $\phi : U\to\mathbb R$ and $\rho:\mathbb R\to\mathbb R$. The function that sends a listing $x_1,\dots,x_M$ of distinct elements of $U$ (any $M\ge 0$) to
--   $$
--   \rho\Bigl(\sum_{m=1}^{M}\phi(x_m)\Bigr)
--   $$
--   is permutation invariant (Property 1).
--
--   This is the sufficiency half of Theorem 2: every function of the form $\rho\left(\sum_{x\in X}\phi(x)\right)$ is a valid set function.
--
--   Differences from the source:
--   - generalization: countable universe 𝔛 → any type U; reason: the argument uses no countability; it specializes to a countable U
--   - encoding: a set X = {x₁, …, x_M} and Σ_{x∈X} φ(x) → an injective tuple x : Fin M → U and Σ_m φ(x m); reason: Lean convention; for distinct x_m the two sums are equal
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12 (PDF p.12), "The sufficiency follows by observing …"

import Mathlib
import Definitions.Def_DeepSets_IsPermInvariant

namespace DeepSets

/-- Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12,
"The sufficiency follows by observing that the function `ρ(∑_{x∈X} φ(x))` satisfies the
permutation invariance condition."

For every `φ : U → ℝ` and `ρ : ℝ → ℝ`, the function `X = {x₁, …, x_M} ↦ ρ(∑_{m=1}^M φ(x_m))`
satisfies Property 1.

**Formalization Note** No countability is assumed: the statement holds for every type `U`. -/
theorem sum_decomposition_isPermInvariant {U : Type*} (φ : U → ℝ) (ρ : ℝ → ℝ) :
    IsPermInvariant (fun (M : ℕ) (x : Fin M → U) => ρ (∑ m, φ (x m))) := by sorry

end DeepSets
