-- Prove2me | Theorems.Thm_BregmanPPA_Convergence_lemma1
-- name    : BregmanPPA.Convergence.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:21:33.976733+00:00
-- url     : https://prove2.me/theorems/69cee2bd-d601-472f-9f5b-b2cce1e52f66
-- title:
--   Lemma 1 — the Bregman resolvent is single-valued and decreases distance to a zero
-- statement:
--   Let $T$ be a monotone operator on a finite-dimensional real inner-product space, and let $h$ be a Bregman function with open zone $S$. For $y\in S$, any point $p\in S$ satisfying $\nabla h(y)-\nabla h(p)\in T(p)$ is unique. If $z\in\overline S$ is a zero of $T$ and such a $p$ exists, then
--
--   $$D_h(z,p)\le D_h(z,y)-D_h(p,y).$$
--
--   This is the resolvent inequality used to control every step of the proximal-point run.
--
--   **Formalization Note** The resolvent is expressed as a relation on $y,p\in S$, which preserves its possible nonexistence. The gradient is evaluated only in $S$; the zero $z$ may lie on the boundary $\overline S\setminus S$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 206, Lemma 1, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open ThreeOpSplitting.Convergence Filter Topology

namespace BregmanPPA.Convergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Lemma 1: uniqueness of the Bregman resolvent and its three-point inequality. -/
theorem lemma1 (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h) :
    (∀ (y p q : H), y ∈ S → p ∈ S → q ∈ S →
      gradient h y - gradient h p ∈ T p →
      gradient h y - gradient h q ∈ T q → p = q) ∧
    (∀ (z y p : H), z ∈ zer T → z ∈ closure S → y ∈ S → p ∈ S →
      gradient h y - gradient h p ∈ T p →
      bregmanD h z p ≤ bregmanD h z y - bregmanD h p y) := by sorry

end BregmanPPA.Convergence
