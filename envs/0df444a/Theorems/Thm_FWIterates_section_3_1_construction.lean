-- Prove2me | Theorems.Thm_FWIterates_section_3_1_construction
-- name    : FWIterates.section_3_1_construction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:00.451893+00:00
-- url     : https://prove2.me/theorems/21dfd130-28ce-4db6-b81c-64e3b444a895
-- title:
--   §3.1, p.5 — the hexagonal sketches $P_k$: nesting, $\bigcap_k P_k = [(-1/4,0),(1/4,0)]$, alignments and constant angles
-- statement:
--   Let $A_k,B_k,C_k,D_k$ and $\mathcal P_k=\operatorname{conv}\{A_k,B_k,C_k,D_k,-D_k,-C_k,-B_k,-A_k\}$ be the points and sketches of §3.1. Then:
--
--   1. there is $(\delta_\ell)\in\,]0,1[^{\mathbb N}$ such that $\lambda\mathcal P_{\ell+1}\subset\operatorname{int}\mathcal P_\ell$ for all $\ell$ and $\lambda\in[1-\delta_\ell,1+\delta_\ell]$, and $0\in\operatorname{int}\mathcal P_\ell$ for all $\ell$ (hypotheses (ii), (iii) of Theorem 3.1); and $B_k$, $C_k$ are vertices of $\mathcal P_k$;
--   2. $\displaystyle\bigcap_{k\in\mathbb N}\mathcal P_k=[(-1/4,0),(1/4,0)]$;
--   3. for all $k$, the points $B_k$, $C_{k+1}$, $(1,0)$ are aligned, and the points $C_k$, $B_{k+1}$, $(-1,0)$ are aligned;
--   4. for all $k$, $\widehat{A_kB_kC_k}=\widehat{A_0B_0C_0}$ and $\widehat{B_kC_kD_k}=\widehat{B_0C_0D_0}$.
--
--   This is the geometry that makes Theorem 3.1 applicable to the sketches and that drives the trajectory of Counterexample 3.5. The claims of the same paragraph about the function $f$ are not part of this item: $\operatorname{arg\,min}_{\mathcal C}f=\bigcap_k\mathcal P_k$ is a conclusion of `FWIterates.section_3_1_trajectory`, and "$\mathcal C$ and $f$ satisfy Assumption 2.3" is part of the goal `FWIterates.counterexample_3_5`.
--
--   **Formalization Note** "Aligned" is `Collinear ℝ`; the angle $\widehat{ABC}$ at $B$ is `EuclideanGeometry.angle A B C`.
--
--   Differences from the source:
--
--   - reading: "f be defined via Theorem 3.1 with A₀ = … and Pₖ = conv{…}", which takes for granted that the sketches satisfy Theorem 3.1's hypotheses → clause 1: some δ ∈ ]0, 1[^ℕ with hypotheses (ii) and (iii), and Bₖ, Cₖ ∈ vert Pₖ; reason: this is what applying Theorem 3.1 to these sketches with the vertices of p.6 requires
--   - reading: "Then C and f satisfy Assumption 2.3 so Theorem 2.4 holds. The solution set is arg min_C f = ⋂ Pₖ = [(−1/4, 0), (1/4, 0)]" → only the f-free equality ⋂ₖ Pₖ = segment [(−1/4, 0), (1/4, 0)]; the claims about f are carried by FWIterates.section_3_1_trajectory (arg min_C f = ⋂ Pₖ) and by the goal FWIterates.counterexample_3_5 (Assumption 2.3); reason: f is not an object of this item
--   - encoding: aligned points; the angle ÂBC → Collinear ℝ {…}; EuclideanGeometry.angle A B C; reason: standard Lean renderings
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, §3.1, p.5, paragraph "Let C = conv{(−1, 0), (0, 1), (1, 0)} and f be defined via Theorem 3.1 …" (from "and Pk = conv{…}" to "in Figure 1")

import Mathlib
import Definitions.Def_FWIterates_sketchPoints

open scoped RealInnerProductSpace Pointwise

namespace FWIterates

/-- **The construction of §3.1** (arXiv:2202.08711v1, §3.1, p.5, "and Pk = conv{…} … B0C0D0").
For the sketches `P_k = conv{A_k, B_k, C_k, D_k, −D_k, −C_k, −B_k, −A_k}` of §3.1:

1. they satisfy hypotheses (ii) and (iii) of Theorem 3.1 for some `(δ ℓ) ∈ ]0, 1[^ℕ`, and `B_k`,
   `C_k` are vertices of `P_k` (so that Theorem 3.1 applies to them);
2. `⋂ k, P_k = [(−1/4, 0), (1/4, 0)]`;
3. for all `k`, the points `B_k, C_{k+1}, (1, 0)` are aligned, and the points `C_k, B_{k+1}, (−1, 0)`
   are aligned;
4. for all `k`, `∠A_kB_kC_k = ∠A₀B₀C₀` and `∠B_kC_kD_k = ∠B₀C₀D₀`.

**Formalization Note** "Aligned" is `Collinear ℝ`; the angle `ABC` at `B` is
`EuclideanGeometry.angle A B C`. Clause 1 states what "f defined via Theorem 3.1 with … P_k" takes
for granted about the sketches; the claim about `f` ("C and f satisfy Assumption 2.3",
`argmin_C f = ⋂ P_k`) is not part of this item. -/
theorem section_3_1_construction :
    (∃ δ : ℕ → ℝ, (∀ ℓ, δ ℓ ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ ℓ, ∀ c ∈ Set.Icc (1 - δ ℓ) (1 + δ ℓ),
        c • sketchPolygon (ℓ + 1) ⊆ interior (sketchPolygon ℓ)) ∧
      (∀ ℓ, (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior (sketchPolygon ℓ))) ∧
    (∀ k, sketchB k ∈ Set.extremePoints ℝ (sketchPolygon k) ∧
      sketchC k ∈ Set.extremePoints ℝ (sketchPolygon k)) ∧
    (⋂ k, sketchPolygon k) = segment ℝ (!₂[-1/4, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1/4, 0] ∧
    (∀ k, Collinear ℝ {sketchB k, sketchC (k + 1), (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))} ∧
      Collinear ℝ {sketchC k, sketchB (k + 1), (!₂[-1, 0] : EuclideanSpace ℝ (Fin 2))}) ∧
    (∀ k, EuclideanGeometry.angle (sketchA k) (sketchB k) (sketchC k) =
        EuclideanGeometry.angle (sketchA 0) (sketchB 0) (sketchC 0) ∧
      EuclideanGeometry.angle (sketchB k) (sketchC k) (sketchD k) =
        EuclideanGeometry.angle (sketchB 0) (sketchC 0) (sketchD 0)) := by sorry

end FWIterates
