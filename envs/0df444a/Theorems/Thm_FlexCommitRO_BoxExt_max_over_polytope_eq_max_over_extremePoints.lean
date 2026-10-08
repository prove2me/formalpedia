-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_max_over_polytope_eq_max_over_extremePoints
-- name    : FlexCommitRO.BoxExt.max_over_polytope_eq_max_over_extremePoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:52.78743+00:00
-- url     : https://prove2.me/theorems/61ed6e93-fa93-4e3d-8bbd-ad8168a6d490
-- title:
--   (38), p. 270 — the worst case of a c.p.f. of an affine image over a polytope equals the worst case over its extreme points
-- statement:
--   Let $\operatorname{val} : \mathbb R^k \to \mathbb R \cup \{+\infty\}$ be a convex polyhedral function, let $D = \operatorname{conv} P \subset \mathbb R^n$ be the convex hull of a finite set $P$ (a convex polytope), and let $B \in \mathbb R^{k\times n}$, $C \in \mathbb R^{k\times m}$, $b \in \mathbb R^k$ and $s \in \mathbb R^m$. Then
--   $$
--   \sup_{d \in D} \operatorname{val}(Bd + Cs + b) = \sup_{d \in \operatorname{ext}(D)} \operatorname{val}(Bd + Cs + b),
--   $$
--   with suprema in $[-\infty, +\infty]$.
--
--   This is the step of the proof of Lemma 2 that replaces the last demand set by its extreme points: the worst case of a convex function over a polytope is attained at a vertex.
--
--   **Formalization Note** The page writes $\operatorname{val}(B_{T+1}d_T + C_{T+1}s_T)$, dropping the $+\,b_{T+1}$ that appears in the definition of $\Phi_T$; the statement keeps it. Values may be $+\infty$; the equality is in the extended reals. With $P = \emptyset$ both sides are $-\infty$.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 270, Appendix, proof of Lemma 2, (38)

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
open Matrix

namespace FlexCommitRO.BoxExt

theorem max_over_polytope_eq_max_over_extremePoints {n m k : ℕ}
    (val : (Fin k → ℝ) → EReal) (hval : IsCPF val)
    (P : Finset (Fin n → ℝ)) (D : Set (Fin n → ℝ)) (hD : D = convexHull ℝ (P : Set (Fin n → ℝ)))
    (Bm : Matrix (Fin k) (Fin n) ℝ) (Cm : Matrix (Fin k) (Fin m) ℝ) (bv : Fin k → ℝ)
    (s : Fin m → ℝ) :
    ⨆ d ∈ D, val (Bm *ᵥ d + Cm *ᵥ s + bv) =
      ⨆ d ∈ D.extremePoints ℝ, val (Bm *ᵥ d + Cm *ᵥ s + bv) := by sorry

end FlexCommitRO.BoxExt
