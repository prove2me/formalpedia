-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_theorem_3_b
-- name    : DataDrivenRO.Guarantee.theorem_3_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:43:11.52513+00:00
-- url     : https://prove2.me/theorems/cbfedd62-0167-476d-97d8-97f0aed71668
-- title:
--   Theorem 3(b), p. 12 — w.p. ≥ 1 − α any x satisfying (9) satisfies the joint chance constraint (7)
-- statement:
--   Under the hypotheses of Theorem 3(a), let $f_1,\dots,f_m$ be functions $f_j(\mathbf u,\mathbf x)$, $\mathbf x\in\mathbb R^k$, each concave in $\mathbf u$ for every $\mathbf x$, and let $\bar\epsilon\in\mathbb R$. Then, with probability at least $1-\alpha$ with respect to the sampling, every $\mathbf x$ that satisfies (9),
--   $$\exists\,\epsilon_1+\dots+\epsilon_m\le\bar\epsilon:\quad f_j(\mathbf u,\mathbf x)\le0\quad\forall\,\mathbf u\in\mathcal U(\mathcal S,\epsilon_j),\ j=1,\dots,m,$$
--   also satisfies the joint chance constraint (7),
--   $$\mathbb P^*\Big(\max_{j=1,\dots,m}f_j(\tilde{\mathbf u},\mathbf x)\le0\Big)\ge1-\bar\epsilon .$$
--
--   The statement holds simultaneously for all such $\mathbf x$ and all admissible $\epsilon_j$, including levels that depend on the data, so (9) can be optimized over the $\epsilon_j$ without losing the guarantee.
--
--   **Formalization Note** The levels range over $\epsilon_j\in(0,1)$, the range on which the family $\mathcal U(\mathcal S,\epsilon)$ is defined; the paper writes $\boldsymbol\epsilon\ge\mathbf 0$. "$\max_j f_j\le0$" is written as "$f_j\le0$ for all $j$". Indices $j$ run over `Fin m`.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, (7) and (9), p. 11, and Theorem 3(b), p. 12 (proof EC.1.2, p. ec2)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- Theorem 3(b), p. 12 (proof EC.1.2, p. ec2). Under the hypotheses of Theorem 3(a), let
`f₁, …, f_m` be constraint functions `f_j(u, x)`, each concave in `u` for every `x`, and let
`ε̄` be given. Then, with probability at least `1 − α` with respect to the sampling, every `x`
satisfying (9) — robust feasibility `f_j(u, x) ≤ 0 ∀ u ∈ U(S, ε_j)` for all `j`, for some
`ε_1, …, ε_m ∈ (0, 1)` with `ε_1 + ⋯ + ε_m ≤ ε̄` — satisfies (7):
`ℙ*(max_j f_j(ũ, x) ≤ 0) ≥ 1 − ε̄`. -/
theorem theorem_3_b {d N k m : ℕ} (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (region : (Fin N → Fin d → ℝ) → Set (Measure (Fin d → ℝ)))
    (U : (Fin N → Fin d → ℝ) → ℝ → Set (Fin d → ℝ))
    (hne : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, (U S ε).Nonempty)
    (hconv : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, Convex ℝ (U S ε))
    (hcpt : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, IsCompact (U S ε))
    (hstep2 : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ P ∈ region S, IsProbabilityMeasure P →
      ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction (U S ε) v)
    (hcover : ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | Pstar ∈ region S})
    (f : Fin m → (Fin d → ℝ) → (Fin k → ℝ) → ℝ)
    (hf : ∀ j x, ConcaveOn ℝ Set.univ (fun u => f j u x)) (εbar : ℝ) :
    ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar)
        {S | ∀ (x : Fin k → ℝ) (εs : Fin m → ℝ), (∀ j, εs j ∈ Set.Ioo (0 : ℝ) 1) →
          ∑ j, εs j ≤ εbar → (∀ j, ∀ u ∈ U S (εs j), f j u x ≤ 0) →
          ENNReal.ofReal (1 - εbar) ≤ Pstar {u | ∀ j, f j u x ≤ 0}} := by sorry

end DataDrivenRO.Guarantee
