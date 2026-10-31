-- Prove2me | Theorems.Thm_DPDeconstructed_display_19
-- name    : DPDeconstructed.display_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:14.002741+00:00
-- url     : https://prove2.me/theorems/bc7789c3-942b-4e1e-b01f-4ce23e555d30
-- title:
--   Display (19) — $M_\sigma h\le Mh$
-- statement:
--   For every feasible policy $\sigma$, every $h:\mathsf F\to\mathbb R$ and every $x\in\mathsf X$,
--
--   $$M_\sigma h(x)=h(x,\sigma(x))\ \le\ \sup_{a\in\Gamma(x)}h(x,a)=Mh(x).$$
--
--   The maximizing operator dominates every policy operator; this is the first inequality in the proof of Theorem 3.2.
--
--   Differences from the source:
--   - generalization: for each h ∈ ℋ → for every h : F → ℝ; reason: the inequality holds for every real function on F; restricting to h ∈ ℋ gives the printed claim
--   - encoding: M_σh ⩽ Mh pointwise → (M_σ h x : EReal) ≤ M h x; reason: M h is an extended-real supremum; same comparison
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §2.5, p.11, display (19)

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

namespace DPDeconstructed

open DynProg

/-- Display (19), Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2,
§2.5, p.11: `M_σ h ⩽ M h` for each `h ∈ ℋ` and `σ ∈ Σ`, pointwise on `X`, where
`M_σ h(x) = h(x, σ(x))` and `M h(x) = sup_{a ∈ Γ(x)} h(x, a)`.

**Formalization Note** The inequality is stated for every `h : F → ℝ`, not only `h ∈ ℋ`, and is
read in `EReal`, where `M h` takes its values. -/
theorem display_19 {X A : Type*} [Nonempty X] (D : DynProg X A) (σ : D.Policy)
    (h : D.SA → ℝ) (x : X) :
    ((D.Mσ σ h x : ℝ) : EReal) ≤ D.M h x := by sorry

end DPDeconstructed
