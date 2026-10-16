-- Prove2me | Theorems.Thm_CompetitiveChores_IndivisibleRounding_theorem_35
-- name    : CompetitiveChores.IndivisibleRounding.theorem_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:37.354988+00:00
-- url     : https://prove2.me/theorems/9d6c7406-b2c7-469e-9a96-554d33bb608d
-- title:
--   Theorem 35, p. 37 — rounding a competitive allocation to an indivisible one competitive at the same prices with budgets satisfying (12)–(13)
-- statement:
--   Rounding of a competitive allocation (Theorem 35, after Barman and Krishnamurthy).
--
--   Let $z$ be a competitive allocation for values $v\in\mathbb R^{n\times m}_{<0}$ and budgets $b\in\mathbb R^n_{<0}$ at prices $p\in\mathbb R^m_{<0}$. Then there is an indivisible allocation $z'$ and budgets $b'\in\mathbb R^n_{\le0}$ such that $z'$ is competitive for $(v,b')$ at the same prices $p$, and $b'$ is close to $b$:
--
--   1. for each agent $i$ with non-empty $z'_i$ there are chores $j\in z'_i$ and $j'\in[m]$ with
--   $$b_i-|p_j|\ \le\ b'_i\ \le\ b_i+|p_{j'}|;\qquad(12)$$
--   2. for each agent $i$ with empty $z'_i$ there is a chore $j'\in[m]$ with
--   $$b_i\ <\ b'_i=0\ <\ b_i+|p_{j'}|.\qquad(13)$$
--
--   Combined with the existence of competitive allocations, this rounding is the main step towards Theorem 34.
--
--   **Formalization Note** Competitiveness for $b'$ is Definition 3 read literally for budgets $b'_i\le0$ (the page writes $b'\in\mathbb R^n_{-\le0}$, meaning $\mathbb R^n_{\le0}$); an agent with $b'_i=0$ is then optimal with the empty bundle. The indivisible allocation is a map $\sigma$ assigning each chore to one agent. The last sentence of the theorem (strongly polynomial running time) is not formalized.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 37, Theorem 35, (12), (13)

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Indivisible

namespace CompetitiveChores.IndivisibleRounding

/-- Theorem 35, p. 37 (Barman and Krishnamurthy): a competitive allocation `z` at prices `p ∈ ℝ^m_{<0}`
for `(v, b)` can be rounded to an indivisible allocation `σ` that is competitive at the same prices `p`
for new budgets `b' ≤ 0` satisfying (12) for agents with non-empty bundles and (13) for agents with
empty bundles. -/
theorem theorem_35 {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i < 0) (z : Fin n → Fin m → ℝ) (p : Fin m → ℝ)
    (hz : CompetitiveChores.RichFamily.IsCompetitiveWith v b z p) :
    ∃ (σ : Fin m → Fin n) (b' : Fin n → ℝ), (∀ i, b' i ≤ 0) ∧
      CompetitiveChores.RichFamily.IsCompetitiveWith v b' (indicator σ) p ∧
      (∀ i, (bundle σ i).Nonempty → ∃ j ∈ bundle σ i, ∃ j' : Fin m,
        b i - |p j| ≤ b' i ∧ b' i ≤ b i + |p j'|) ∧
      (∀ i, bundle σ i = ∅ → ∃ j' : Fin m, b i < b' i ∧ b' i = 0 ∧ 0 < b i + |p j'|) := by sorry

end CompetitiveChores.IndivisibleRounding
