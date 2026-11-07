-- Prove2me | Theorems.Thm_CtxSearchTSR_remark_2_3
-- name    : CtxSearchTSR.remark_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:08.070421+00:00
-- url     : https://prove2.me/theorems/93f9cff3-cab1-4b78-bbe8-4a0bf6d9a302
-- title:
--   Remark 2.3 — $uu^\top/a\preceq R$ and $R-uu^\top/(4a)\succeq\tfrac34R\succ0$
-- statement:
--   Let $R\in\mathbb R^{d\times d}$ be symmetric positive definite and $x\in\mathbb R^d$ with $x\neq0$. Write $u=Rx$ and $a=x^\top Rx$. Then:
--
--   1. (Cauchy–Schwarz in the $R$-inner product) for every $v\in\mathbb R^d$, $(v^\top u)^2\le(v^\top Rv)(x^\top Rx)$;
--   2. $uu^\top/a\preceq R$;
--   3. the update (10) of Algorithm 2 with $\varepsilon,Y\in\{-1,1\}$ and $\varepsilon Y=-1$ has scale matrix $R-uu^\top/(4a)$;
--   4. $R-uu^\top/(4a)-\tfrac34R\succeq0$;
--   5. $\tfrac34R\succ0$;
--   6. hence $R-uu^\top/(4a)\succ0$.
--
--   In display,
--
--   $$R-\frac{uu^\top}{4a}\succeq\frac34R\succ0.$$
--
--   This is the step that makes Algorithm 2 well defined: the scale matrix stays positive definite after an inward update.
--
--   **Formalization Note** $A\preceq B$ is "$B-A$ is positive semidefinite".
--
--   Differences from the source:
--   - reading: "R − uu⊤/4a" → R − (4a)⁻¹ uuᵀ; reason: the value of the update (10) at εY = −1 is R − uuᵀ/(a·4)
--   - reading: "the update rule in (10) satisfies R − uu⊤/4a ⪰ 3/4 R ≻ 0" → a clause identifying the update (10) at εY = −1 with R − uuᵀ/(4a), plus the matrix inequalities for that matrix; reason: the sentence asserts both that the update equals this matrix and the inequalities
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §2.2, Remark 2.3, p.10

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **Remark 2.3 (R_t ≻ 0 throughout execution).** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), p.10.

"Assume R ≻ 0 and x ≠ 0, and write u = Rx and a = xᵀRx. Cauchy–Schwarz in the inner product
induced by R gives (vᵀu)² ≤ (vᵀRv)(xᵀRx) for every v ∈ ℝ^d. Hence uuᵀ/a ⪯ R, and the update rule
in (10) satisfies R − uuᵀ/4a ⪰ 3/4 R ≻ 0."

The six clauses are: the Cauchy–Schwarz inequality; uuᵀ/a ⪯ R; the update (10) with e, Y ∈ {−1, 1} and εY = −1 has
scale matrix R − uuᵀ/(4a); R − uuᵀ/(4a) − (3/4)R ⪰ 0; (3/4)R ≻ 0; and the conclusion
R − uuᵀ/(4a) ≻ 0. The remark's last sentence (induction over the rounds) is
`section_2_2_posDef_preserved`.

**Formalization Note.** `A ⪯ B` is `(B - A).PosSemidef`; R ≻ 0 is `R.PosDef` (symmetric
positive definite). "uuᵀ/4a" is read uuᵀ/(4a), the value of the update (10) at εY = −1. -/
theorem remark_2_3 {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosDef) (x : Fin d → ℝ)
    (hx : x ≠ 0) :
    let u := R *ᵥ x
    let a := x ⬝ᵥ (R *ᵥ x)
    (∀ v : Fin d → ℝ, (v ⬝ᵥ u) ^ 2 ≤ (v ⬝ᵥ (R *ᵥ v)) * (x ⬝ᵥ (R *ᵥ x))) ∧
    (R - a⁻¹ • vecMulVec u u).PosSemidef ∧
    (∀ (m : Fin d → ℝ) (e Y : ℝ), ((e = 1 ∧ Y = -1) ∨ (e = -1 ∧ Y = 1)) →
      (update ⟨m, R⟩ x e Y).R = R - (4 * a)⁻¹ • vecMulVec u u) ∧
    (R - (4 * a)⁻¹ • vecMulVec u u - (3 / 4 : ℝ) • R).PosSemidef ∧
    ((3 / 4 : ℝ) • R).PosDef ∧
    (R - (4 * a)⁻¹ • vecMulVec u u).PosDef := by sorry

end CtxSearchTSR
