-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_C_3
-- name    : AdaptiveSparsify.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:44.77425+00:00
-- url     : https://prove2.me/theorems/bb308aef-4c28-451e-88e7-3b10911491a3
-- title:
--   Lemma C.3 — Hessians of two well-centered points differ by at most $O_{C_K}(n^2r^2)$
-- statement:
--   Let $(x,s)$ and $(\hat x,\hat s)$ be $\varepsilon$ well-centered at path parameters $t,\hat t$, for $\varepsilon<1/1000$, and let $r=\max\{\hat t/t,t/\hat t\}$. Then for $h=Cn^2r^2$, with $C$ depending only on $C_K$,
--
--   $$\frac{\nabla^2\Phi_i(x_i)}{h}\preceq\nabla^2\Phi_i(\hat x_i)\preceq h\nabla^2\Phi_i(x_i)\qquad\text{for all }i\in[m].$$
--
--   So the matrix given to Theorem 3 stays polynomially conditioned along the whole central path.
--
--   Differences from the source:
--   - reading: §4 assumes n large enough for log n > 0 → n ≥ 2; reason: λ = C_center log n / ε² vanishes at n = 1 and α is then undefined
--   - reading: C_center implicit in "well-centered" → C_center ≥ 1; reason: under which α is small for ε < 1/1000 and n ≥ 2, as the proof needs
--   - reading: h = O_{C_K}(n²r²) → h = C n² r² with C depending on C_K only; reason: the barrier parameters are at most C_K, p.70
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma C.3, p.70

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

open Matrix

namespace AdaptiveSparsify

/-- **Lemma C.3**, p.70.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma C.3, p.70.

"Let (x, s) and (x̂, ŝ) be ε-well-centered solutions for ε < 1/1000 and path parameters t, t̂. Then for
r = max{t̂/t, t/t̂} and h = O_{C_K}(n²r²) it holds that ∇²Φ_i(x_i)/h ⪯ ∇²Φ_i(x̂_i) ⪯ h∇²Φ_i(x_i) for all i ∈ [m]."

**Formalization Note.** Well-centeredness is Definition 4.2 with the `α` of §4 and `C_center ≥ 1`, under
which `α` is small. The constant `C` depends on `C_K` only, the barrier parameters being bounded by `C_K`
(p.70). -/
theorem lemma_C_3 : ∀ CK : ℕ, 1 ≤ CK → ∃ C : ℝ, 0 < C ∧
    ∀ (ε Cc : ℝ), 0 < ε → ε < 1 / 1000 → 1 ≤ Cc →
    ∀ I : ERMInstance, I.IsAdmissible CK → 2 ≤ I.blocks.n →
    ∀ (t th : ℝ) (x s xh sh : Fin I.blocks.n → ℝ), 0 < t → 0 < th →
      let p : Params := ⟨CK, ε, Cc⟩
      let α := p.alpha I.blocks.n
      I.WellCentered α ε t x s → I.WellCentered α ε th xh sh →
      let r := max (th / t) (t / th)
      let h := C * (I.blocks.n : ℝ) ^ 2 * r ^ 2
      ∀ i, LoewnerLE (h⁻¹ • I.hess x i) (I.hess xh i) ∧
        LoewnerLE (I.hess xh i) (h • I.hess x i) := by sorry

end AdaptiveSparsify
