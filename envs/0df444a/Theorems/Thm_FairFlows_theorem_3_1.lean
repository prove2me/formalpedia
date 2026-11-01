-- Prove2me | Theorems.Thm_FairFlows_theorem_3_1
-- name    : FairFlows.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:08.247376+00:00
-- url     : https://prove2.me/theorems/72d696df-3b33-4670-9efa-ba194b171f7a
-- title:
--   Theorem 3.1 — the covering system $[A_Lx_L\ge p,\ x_L\le1,\ x_L\ge0]$ is TDI, with integral and laminar optima
-- statement:
--   Let $p:2^V\to\mathbb Z\cup\{-\infty\}$ be an intersecting supermodular set function and let the digraph $D_L=(V,L)$ cover $p$. Then:
--
--   1. the linear inequality system $[A_Lx_L\ge p,\ x_L\le 1,\ x_L\ge 0]$ is totally dual integral;
--   2. the primal program $$\min\{\mathbf 1x_L: A_Lx_L\ge p,\ x_L\le 1,\ x_L\ge 0\}\qquad(3.2)$$ and the dual program $$\max\{yp-\mathbf 1z: yA_L-z\le\mathbf 1,\ (y,z)\ge0\}\qquad(3.3)$$ have integer-valued optimal solutions;
--   3. there is an integer-valued dual optimum $(y^*,z^*)$ whose support family $\{Z: y^*(Z)>0\}$ is laminar.
--
--   The result is cited from Frank (1979) and Theorem 17.1.1 of Frank's book; it yields the min-max formula of Theorem 3.2 for the smallest covering edge set.
--
--   **Formalization Note** The hypothesis that $D_L$ covers $p$ is the standing assumption of p.7. TDI is the published `BoxTDIMinMax.Separable.IsTDI`.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: a digraph D_L = (V, L) → an edge subset L of a digraph D (D_L is D with L = all edges); reason: Lean convention; same instances
--   - encoding: "[A_L x_L ≥ p, x_L ≤ 1, x_L ≥ 0] is TDI" → the published IsTDI (for every integral c with max{y b : y ≥ 0, y M = c} finite, the maximum has an integral optimal solution) applied to M = [A_L; I; −I], b = [p; 0; −1]; reason: the standard definition of TDI for the system written as M x ≥ b; same instances
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 3.1, p.8 (standing assumption p.7)

import Mathlib
import Definitions.Def_FairFlows_CoverLP

set_option autoImplicit false

namespace FairFlows

/-- Theorem 3.1 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.8; cited from Frank 1979 and Theorem 17.1.1 of Frank's book).
Let `D_L = (V, L)` cover the intersecting supermodular set function `p : 2^V → ℤ ∪ {−∞}`. Then
the system `[A_L x_L ≥ p, x_L ≤ 1, x_L ≥ 0]` is TDI; the primal program
`min{1 x_L : A_L x_L ≥ p, x_L ≤ 1, x_L ≥ 0}` (3.2) and the dual program
`max{y p − 1 z : y A_L − z ≤ 1, (y, z) ≥ 0}` (3.3) have integer-valued optimal solutions; and
some integer-valued dual optimum `(y*, z*)` has a laminar support family `{Z : y*(Z) > 0}`.

**Formalization Note** `D_L` is the edge subset `L` of `D`; the hypothesis that `D_L` covers `p`
is the standing assumption of p.7. Rows of `A_L` are the sets with `p(X) > −∞`. -/
theorem theorem_3_1 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (L : Finset A) (p : Finset V → WithBot ℤ)
    (hp : IsIntersectingSupermodular p) (hcov : Covers D L p) :
    IsCoverTDI D L p ∧
    (∃ x, IsCoverPrimalOpt D L p (fun _ => 1) x ∧ IsIntegral x) ∧
    (∃ y z, IsCoverDualOpt D L p (fun _ => 1) y z ∧ IsIntegral y ∧ IsIntegral z) ∧
    (∃ y z, IsCoverDualOpt D L p (fun _ => 1) y z ∧ IsIntegral y ∧ IsIntegral z ∧
      IsLaminar (dualSupport y)) := by sorry

end FairFlows
