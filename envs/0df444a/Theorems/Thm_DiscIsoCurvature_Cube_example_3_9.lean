-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_example_3_9
-- name    : DiscIsoCurvature.Cube.example_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:08:39.849757+00:00
-- url     : https://prove2.me/theorems/f4dccf70-ce5e-454c-83d2-b6951e7f2363
-- title:
--   Example 3.9 — canonical I⋆, A⋆, J⋆ versus Inf_µ, SA_µ, SqInf_µ for Boolean f
-- statement:
--   Let $\mu$ be a fully supported distribution on $\Omega=\{\pm1\}^n$, with canonical rates $q^\star_i(x)=\frac12\sqrt{\mu(x^i)/\mu(x)}$ and weights $w^\star_i=2q^\star_i$, and write $I^\star$, $A^\star$, $J^\star$ for $I_{w^\star}$, $A_{w^\star}$, $J_{w^\star}$ under $q^\star$. For every Boolean $f:\Omega\to\{\pm1\}$:
--
--   1. $I^\star_i(f)=\mathrm{Inf}_{\mu,i}(f)$ for every $i$, and $I^\star(f)=\sum_iI^\star_i(f)$;
--   2. $A^\star(f)=\mathbb E_\mu\big[\sqrt{s_\mu(f)}\big]$ with $s_\mu(f)(x)=\sum_i\frac{\mu(x^i)}{\mu(x)}\mathbf 1\{f(x^i)\ne f(x)\}$; and if $b\le\sqrt{\mu(x^i)/\mu(x)}\le1/b$ for all $i,x$, for some $b\in(0,1]$, then $bA^\star(f)\le\mathrm{SA}_\mu(f)\le\frac1bA^\star(f)$;
--   3. $J^\star(f)=\sum_i\mathbb E_\mu\big[\sqrt{\mu(x^i)/\mu(x)}\,\mathbf 1\{f(x^i)\ne f(x)\}\big]^2$; and under the same bound $b^2J^\star(f)\le\mathrm{SqInf}_\mu(f)\le\frac1{b^2}J^\star(f)$.
--
--   $$\mathrm{Inf}_{\mu,i}=I^\star_i,\qquad bA^\star\le\mathrm{SA}_\mu\le A^\star/b,\qquad b^2J^\star\le\mathrm{SqInf}_\mu\le J^\star/b^2 .$$
--   These comparisons convert the canonical inequalities of §5–§6 into Theorem 1.1.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: f : Ω → {±1} → f : Ω → ℝ with IsBoolean f; reason: the same functions
--   - encoding: the identities E_µ[√(s(f))] = SA_µ(f) and ∑ᵢ Pr_µ[f(x^i) ≠ f(x)]² = SqInf_µ(f) inside the displayed chains → SA_µ(f) and SqInf_µ(f) by their definitions; reason: these equalities are the definitions of §1.1
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 16, Example 3.9

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Influence
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup

namespace DiscIsoCurvature.Cube

/-- Example 3.9 (p. 16): for `μ` fully supported on `{±1}^n`, canonical rates `q⋆` and weights
`w⋆`, and Boolean `f`:
(1) `I⋆ᵢ(f) = Inf_{μ,i}(f)` for every `i`, and `I⋆(f) = ∑ᵢ I⋆ᵢ(f)`;
(2) `A⋆(f) = E_μ[√(s_μ(f))]`, `s_μ(f)(x) = ∑ᵢ (μ(x^i)/μ(x)) 1{f(x^i) ≠ f(x)}`, and if
`b ≤ √(μ(x^i)/μ(x)) ≤ 1/b` for all `i, x` (`b ∈ (0, 1]`) then `b A⋆(f) ≤ SA_μ(f) ≤ A⋆(f)/b`;
(3) `J⋆(f) = ∑ᵢ E_μ[√(μ(x^i)/μ(x)) 1{f(x^i) ≠ f(x)}]²`, and under the same bound
`b² J⋆(f) ≤ SqInf_μ(f) ≤ J⋆(f)/b²`. -/
theorem example_3_9 {n : ℕ} (μ : BoolCube n → ℝ) (hμ : IsFullDist μ) (f : BoolCube n → ℝ)
    (hf : IsBoolean f) :
    ((∀ i, wInfluenceI μ (wStar μ) (qStar μ) i f = influence μ f i) ∧
      wInfluence μ (wStar μ) (qStar μ) f = ∑ i, wInfluenceI μ (wStar μ) (qStar μ) i f) ∧
    (wSurfaceArea μ (wStar μ) (qStar μ) f =
        expect μ (fun x => Real.sqrt
          (∑ i, μ (flip x i) / μ x * (if f (flip x i) ≠ f x then 1 else 0))) ∧
      ∀ b : ℝ, 0 < b → b ≤ 1 →
        (∀ i x, b ≤ Real.sqrt (μ (flip x i) / μ x) ∧ Real.sqrt (μ (flip x i) / μ x) ≤ 1 / b) →
        b * wSurfaceArea μ (wStar μ) (qStar μ) f ≤ surfaceArea μ f ∧
          surfaceArea μ f ≤ (1 / b) * wSurfaceArea μ (wStar μ) (qStar μ) f) ∧
    (wSqInfluence μ (wStar μ) (qStar μ) f =
        ∑ i, (expect μ (fun x => Real.sqrt (μ (flip x i) / μ x) *
          (if f (flip x i) ≠ f x then 1 else 0))) ^ 2 ∧
      ∀ b : ℝ, 0 < b → b ≤ 1 →
        (∀ i x, b ≤ Real.sqrt (μ (flip x i) / μ x) ∧ Real.sqrt (μ (flip x i) / μ x) ≤ 1 / b) →
        b ^ 2 * wSqInfluence μ (wStar μ) (qStar μ) f ≤ sqInfluence μ f ∧
          sqInfluence μ f ≤ (1 / b ^ 2) * wSqInfluence μ (wStar μ) (qStar μ) f) := by sorry

end DiscIsoCurvature.Cube
