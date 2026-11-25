-- Prove2me | Theorems.Thm_ErdosDyadic_dyadic_not_measure_universal
-- name    : ErdosDyadic.dyadic_not_measure_universal
-- status  : Open
-- author  : @Jhon Lenin Acuna
-- created : 2026-11-25T04:45:42.751834+00:00
-- url     : https://prove2.me/theorems/f11a7eb4-b6f5-40cb-9ce9-8ce3bd645810
-- title:
--   Dyadic case of the Erdős similarity conjecture (Theorem 1.1)
-- statement:
--   **Theorem 1.1.** Let $D=\{2^{-n}:n\ge1\}$. For every $\eta\in(0,1)$ there is a compact set $E_\eta\subseteq[0,1]$ with
--   $$m(E_\eta)>1-\eta$$
--   such that
--   $$\text{for every } x\in\mathbb R \text{ and every } s\in\mathbb R\setminus\{0\}:\qquad x+sD\not\subseteq E_\eta .$$
--
--   Since $m(E_\eta)>0$, no set containing $E_\eta$ is forced to contain an affine copy of $D$, so $D$ is not measure universal: the Erdős similarity conjecture holds for this one infinite pattern. The statement concerns $D$ only, not arbitrary infinite sets.
--
--   **Formalization Note** Lean states the explicit avoiding-set form above; "$D$ is not measure universal" is its consequence and is not defined separately. The measure bound is stated in $[0,\infty]$ via `ENNReal.ofReal (1 - η)`; both signs of $s$ are covered because $s$ ranges over all nonzero reals.
-- source:
--   OpenAI, The dyadic case of the Erdős similarity conjecture, Sept 25, 2026, https://github.com/openai/math/tree/main/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026, Theorem 1.1, p. 2 (proof in Section 6, pp. 14-15)

import Mathlib
import Definitions.Def_erdos_dyadic_D

open MeasureTheory Set

namespace ErdosDyadic

/-- Theorem 1.1: an explicit compact set of measure > 1 - η avoiding all signed affine copies of D. -/
theorem dyadic_not_measure_universal (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) 1) :
    ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc 0 1 ∧ volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ¬ ((fun d : ℝ => x + s * d) '' D ⊆ E) := by
  sorry

end ErdosDyadic
