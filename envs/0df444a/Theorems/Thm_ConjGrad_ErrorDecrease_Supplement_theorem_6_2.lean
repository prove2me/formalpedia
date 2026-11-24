-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_6_2
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:57:56.461838+00:00
-- url     : https://prove2.me/theorems/45f9162e-8ffe-4897-9673-bf9afed88ab8
-- title:
--   Theorem 6:2 — $x_i$ is the point of the convex hull $S_i$ nearest to $h$
-- statement:
--   Let $x_0,x_1,\dots$ be the estimates of the cg-method for a real symmetric positive definite $A$ with $Ah=k$, and let $S_i$ be the convex closure of $x_0,\dots,x_i$. Then $x_i\in S_i$ and $x_i$ is the point of $S_i$ whose error vector $h-x$ is the shortest: for every $x\in S_i$ with $x\ne x_i$,
--
--   $$|h-x_i|<|h-x| .$$
--
--   The estimates thus approach $h$ in the Euclidean metric as well as in the energy metric $f$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410.
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 416, Theorem 6:2 (PDF p. 8)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:2 (Hestenes–Stiefel 1952, p. 416): `xᵢ` is the unique point of the convex hull
`Sᵢ` of `x₀, …, xᵢ` with the shortest error vector `h − x`. -/
theorem theorem_6_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    (cgIter A k x₀ i).x ∈ convexHull ℝ (Set.range fun j : Fin (i + 1) => (cgIter A k x₀ j).x) ∧
    ∀ y ∈ convexHull ℝ (Set.range fun j : Fin (i + 1) => (cgIter A k x₀ j).x),
      y ≠ (cgIter A k x₀ i).x →
      (h - (cgIter A k x₀ i).x) ⬝ᵥ (h - (cgIter A k x₀ i).x) < (h - y) ⬝ᵥ (h - y) := by sorry

end ConjGrad.ErrorDecrease.Supplement
