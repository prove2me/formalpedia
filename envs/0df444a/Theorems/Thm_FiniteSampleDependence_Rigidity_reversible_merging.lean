-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_reversible_merging
-- name    : FiniteSampleDependence.Rigidity.reversible_merging
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:10.378366+00:00
-- url     : https://prove2.me/theorems/b61d7615-bbd8-4188-b1d8-1f816e9e5959
-- title:
--   Lemma 3.1 — reversible merging of proportional rows
-- statement:
--   Let $n,m\ge2$ and let $F$ satisfy (LF-DPI) on $\Delta_{n,m}$. For distinct rows $i\ne j$ and every $U\in\Delta_{n,m}$,
--   $$F(M_{ij}U)\le F(U),$$
--   where $M_{ij}$ replaces row $i$ by $U_{i\bullet}+U_{j\bullet}$ and row $j$ by zero. Moreover equality $F(M_{ij}U)=F(U)$ holds whenever $U_{i\bullet}=a v$ and $U_{j\bullet}=b v$ for some scalars $a,b\ge0$ and some vector $v\ge0$ (the case $a=b=0$ included).
--
--   Merging two proportional rows is reversible by a channel, so it does not change the value; this is the basic move of the zero-row argument.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: a functional F : Δ_{n,m} → ℝ on the simplex → a function F on all real n×m matrices, of which only the values on Δ_{n,m} enter the hypotheses and conclusion; reason: every hypothesis and conclusion quantifies over U ∈ Δ_{n,m} (and TU, M_{ij}U, QU stay in Δ_{n,m}), so the values off the simplex are irrelevant; every functional on Δ_{n,m} extends
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Lemma 3.1, PDF p. 7 (printed p. 6)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

namespace FiniteSampleDependence.Rigidity

/-- Lemma 3.1 (Reversible merging). If `F` satisfies (LF-DPI), then for distinct rows `i ≠ j`
and every `U ∈ Δ_{n,m}`, `F(M_{ij} U) ≤ F(U)`, with equality whenever `U_{i•} = a v` and
`U_{j•} = b v` for some `a, b ≥ 0` and `v ≥ 0`. -/
theorem reversible_merging {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F) (i j : Fin n) (hij : i ≠ j)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) :
    F (mergeMatrix i j * U) ≤ F U ∧
    ∀ (a b : ℝ) (v : Fin m → ℝ), 0 ≤ a → 0 ≤ b → (∀ α, 0 ≤ v α) →
      (∀ α, U i α = a * v α) → (∀ α, U j α = b * v α) →
      F (mergeMatrix i j * U) = F U := by sorry

end FiniteSampleDependence.Rigidity
