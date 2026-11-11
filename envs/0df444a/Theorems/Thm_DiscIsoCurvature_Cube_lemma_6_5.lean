-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_lemma_6_5
-- name    : DiscIsoCurvature.Cube.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:09:25.22769+00:00
-- url     : https://prove2.me/theorems/209b0941-ad28-4e8d-94b9-4978db99e089
-- title:
--   Lemma 6.5 — the adapted commutator inequality (L|∇⋆| − sgn(∇⋆g) ⊙ ∇⋆L) g ≥ (D + diag{M1} − |M|ᵀ)|∇⋆|g
-- statement:
--   Let $\mu$ be a fully supported distribution on $\Omega=\{\pm1\}^n$, with canonical rates $q^\star$, weights $w^\star$, generator $L$, and $\delta^\star_i=\delta_{w^\star,i}$. Let $M$, $D$ be the matrix fields (49), (51) and $|M|=(|M_{ij}|)$. For every $g:\Omega\to\mathbb R$, every $x$ and every coordinate $i$,
--   $$L\big(|\delta^\star_i g|\big)(x)-\mathrm{sgn}\big(\delta^\star_ig(x)\big)\,\delta^\star_i(Lg)(x)\ \ge\ \sum_{j}\Big(D(x)+\mathrm{diag}\{M(x)\mathbf 1\}-|M(x)|^\top\Big)_{ij}\,|\delta^\star_jg(x)|,$$
--   with $\mathrm{sgn}(0)=0$. This is the vector inequality $(L|\nabla^\star|-\mathrm{sgn}(\nabla^\star g)\odot\nabla^\star L)g\ge(D+\mathrm{diag}\{M\mathbf1\}-|M|^\top)|\nabla^\star|g$, read coordinate by coordinate and pointwise. It is the commutator estimate behind the CSGE bound of Theorem 6.4.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - encoding: vector inequality between vector fields → for every x and every coordinate i; reason: the paper's entrywise, pointwise order (§4.1)
--   - encoding: sgn with sgn(0) = 0 → Real.sign; reason: Real.sign 0 = 0, Real.sign a = ±1 otherwise
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 36, Lemma 6.5

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Semigroup
import Definitions.Def_DiscIsoCurvature_Cube_Curvature

namespace DiscIsoCurvature.Cube

/-- Lemma 6.5 (p. 36): for `μ` fully supported on `{±1}^n`, canonical rates `q⋆` and weights
`w⋆`, and every `g : Ω → ℝ`, pointwise at every `x` and in every coordinate `i`,
`(L|∇⋆| − sgn(∇⋆g) ⊙ ∇⋆L) g ≥ (D + diag{M1} − |M|ᵀ) |∇⋆| g`, i.e.
`L(|δ⋆ᵢ g|)(x) − sgn(δ⋆ᵢ g(x)) · δ⋆ᵢ(Lg)(x) ≥ ∑ⱼ (D(x) + diag{M(x)1} − |M(x)|ᵀ)ᵢⱼ |δ⋆ⱼ g(x)|`,
with `sgn 0 = 0` (`Real.sign`), `M`, `D` the matrix fields (49), (51). -/
theorem lemma_6_5 {n : ℕ} (μ : BoolCube n → ℝ) (hμ : IsFullDist μ) (g : BoolCube n → ℝ)
    (x : BoolCube n) (i : Fin n) :
    ((matD μ x + Matrix.diagonal ((matM μ x).mulVec (fun _ => 1))
        - Matrix.transpose ((matM μ x).map (fun a => |a|))).mulVec
        (fun j => absDelta (wStar μ) (qStar μ) j g x)) i ≤
      gen (qStar μ) (absDelta (wStar μ) (qStar μ) i g) x
        - Real.sign (delta (wStar μ) (qStar μ) i g x)
            * delta (wStar μ) (qStar μ) i (gen (qStar μ) g) x := by sorry

end DiscIsoCurvature.Cube
