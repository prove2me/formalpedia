-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_nonnegativity_permutation_invariance
-- name    : FiniteSampleDependence.Rigidity.nonnegativity_permutation_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:20.967193+00:00
-- url     : https://prove2.me/theorems/b37042ac-519f-412c-a2ab-956113861aa2
-- title:
--   Lemma 2.1 — (LF-DPI) and (IZ) imply $F\ge0$; (LF-DPI) implies row-permutation invariance
-- statement:
--   Let $n,m\ge2$ and let $F$ be a functional on $\Delta_{n,m}$.
--
--   1. If $F$ satisfies (LF-DPI) and (IZ), then $F(U)\ge0$ for every $U\in\Delta_{n,m}$.
--   2. If $F$ satisfies (LF-DPI), then for every permutation matrix $Q\in\mathbb R^{n\times n}$ and every $U\in\Delta_{n,m}$,
--   $$F(QU)=F(U).$$
--
--   The second clause does not use (IZ). Together they say that any admissible dependence measure is nonnegative and does not depend on how the states of the processed variable are labelled.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: a functional F : Δ_{n,m} → ℝ on the simplex → a function F on all real n×m matrices, of which only the values on Δ_{n,m} enter the hypotheses and conclusion; reason: every hypothesis and conclusion quantifies over U ∈ Δ_{n,m} (and TU, M_{ij}U, QU stay in Δ_{n,m}), so the values off the simplex are irrelevant; every functional on Δ_{n,m} extends
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: row permutation matrix Q → σ.permMatrix ℝ, with σ ranging over all permutations of Fin n; reason: every permutation matrix has this form, so the same matrices are quantified over
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Lemma 2.1, PDF p. 6 (printed p. 5)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

namespace FiniteSampleDependence.Rigidity

/-- Lemma 2.1 (Nonnegativity and permutation invariance). (LF-DPI) and (IZ) imply `F ≥ 0` on
`Δ_{n,m}`; (LF-DPI) alone implies `F(QU) = F(U)` for every row permutation matrix `Q`. -/
theorem nonnegativity_permutation_invariance {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) :
    (LFDPI F → IZ F → ∀ U ∈ simplex n m, 0 ≤ F U) ∧
    (LFDPI F → ∀ σ : Equiv.Perm (Fin n), ∀ U ∈ simplex n m,
      F (σ.permMatrix ℝ * U) = F U) := by sorry

end FiniteSampleDependence.Rigidity
