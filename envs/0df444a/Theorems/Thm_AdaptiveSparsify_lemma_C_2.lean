-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_C_2
-- name    : AdaptiveSparsify.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:57.22628+00:00
-- url     : https://prove2.me/theorems/d8877fda-df70-467b-b005-6939d14a5685
-- title:
--   Lemma C.2 — a bounded symmetrized gradient product compares the Hessians up to $O(\nu^2M^2)$
-- statement:
--   Let $K$ be convex and $\Phi$ a $\nu$-self-concordant barrier on $\operatorname{int}K$. For any $M\ge1$ and $x,y\in\operatorname{int}K$ with
--
--   $$\langle\nabla\Phi(y)-\nabla\Phi(x),y-x\rangle\le M,$$
--
--   we have $h^{-1}\nabla^2\Phi(x)\preceq\nabla^2\Phi(y)\preceq h\nabla^2\Phi(x)$ for $h=C\nu^2M^2$, with $C$ an absolute constant. It bounds how far Hessians can drift along the path, and thereby the condition number given to Theorem 3.
--
--   Differences from the source:
--   - reading: x, y ∈ K → x, y ∈ int K; reason: ∇Φ exists only on int K
--   - reading: h = O(ν²M²) → h = C ν² M² with C absolute, chosen first; reason: the meaning of O
--   - encoding: Definition 3.1 of a ν-self-concordant function → the published IsNuSelfConcordantBarrier; reason: the line form of Definition 3.1, by polarization (reading R9)
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma C.2, p.69

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_AdaptiveSparsify_Linear

open Matrix

namespace AdaptiveSparsify

/-- **Lemma C.2**, p.69.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma C.2, p.69.

"Let K be a convex set and Φ : int(K) → R be a ν-self-concordant function. For any parameter M ≥ 1 any
x, y ∈ K with ⟨∇Φ(y) − ∇Φ(x), y − x⟩ ≤ M, we have h⁻¹∇²Φ(x) ⪯ ∇²Φ(y) ⪯ h∇²Φ(x) for some h = O(ν²M²)."

**Formalization Note.** `x, y ∈ int K`: `∇Φ` exists only there. `h = C ν² M²` with `C` absolute. -/
theorem lemma_C_2 : ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin k)))
    (Φ : EuclideanSpace ℝ (Fin k) → ℝ) (ν M : ℝ) (x y : Fin k → ℝ),
    Convex ℝ K → EntropicBarrier.Universal.IsNuSelfConcordantBarrier K Φ ν → 1 ≤ M →
    WithLp.toLp 2 x ∈ interior K → WithLp.toLp 2 y ∈ interior K →
    (gradVec Φ y - gradVec Φ x) ⬝ᵥ (y - x) ≤ M →
    LoewnerLE ((C * ν ^ 2 * M ^ 2)⁻¹ • hessMat Φ x) (hessMat Φ y) ∧
    LoewnerLE (hessMat Φ y) ((C * ν ^ 2 * M ^ 2) • hessMat Φ x) := by sorry

end AdaptiveSparsify
