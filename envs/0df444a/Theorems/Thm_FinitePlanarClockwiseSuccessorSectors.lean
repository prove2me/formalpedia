-- Prove2me | Theorems.Thm_FinitePlanarClockwiseSuccessorSectors
-- name    : FinitePlanarClockwiseSuccessorSectors
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T20:26:00.662977+00:00
-- url     : https://prove2.me/theorems/c115f72f-3a63-4fc7-bbdf-17025fc2c487
-- title:
--   Finite Planar Clockwise Successor Sectors
-- statement:
--   Let $\iota$ be a nonempty finite set, let $p\in\mathbb R^2$, let
--   $\rho>0$, and assign to every $i\in\iota$ a nonzero direction
--   $u_i\in\mathbb R^2$.  Assume distinct indices determine distinct positive
--   rays: if $u_j=t u_i$ for some $t>0$, then $j=i$.  Then there are a
--   permutation $\operatorname{next}$ of $\iota$, a full clockwise turn
--   $T=2\pi$, positive clockwise turns $T(i,j)\in(0,T]$, and sets
--   $\Sigma_i\subset\mathbb R^2$ with the following properties.
--
--   The full turn occurs exactly on the same germ,
--   $$
--     T(i,j)=T \quad\Longleftrightarrow\quad j=i,
--   $$
--   $\operatorname{next}(i)$ has minimal positive clockwise turn from $i$,
--   and
--   $$
--     \operatorname{next}(i)=i
--     \quad\Longleftrightarrow\quad
--     \text{$i$ is the only element of $\iota$}.
--   $$
--   If $i$ is the only germ, then
--   $$
--     \Sigma_i=
--     B(p,\rho)\setminus
--     \bigl(\{p+t u_i:t>0\}\cup\{p\}\bigr).
--   $$
--   Otherwise there are real numbers $c_i,s_i$, with $s_i\ne0$ or $c_i<0$,
--   such that
--   $$
--     u_{\operatorname{next}(i)}
--       =c_i u_i-s_i\operatorname{rot}_{90}(u_i).
--   $$
--   Writing
--   $$
--     \Phi_i(x,y)=p+xu_i+y\operatorname{rot}_{90}(u_i),
--   $$
--   the sector $\Sigma_i$ is
--   $$
--    \begin{cases}
--    \Phi_i\{(x,y):x^2+y^2<(\rho/\|u_i\|)^2,\ y<0,\
--      c_i y+s_i x>0\}, & s_i>0,\\
--    \Phi_i\{(x,y):x^2+y^2<(\rho/\|u_i\|)^2,\
--      (y<0\text{ or }c_i y+s_i x>0)\}, & s_i<0,\\
--    \Phi_i\{(x,y):x^2+y^2<(\rho/\|u_i\|)^2,\ y<0\}, & s_i=0.
--    \end{cases}
--   $$
--   Each $\Sigma_i$ is open and connected, is contained in $B(p,\rho)$, and
--   is disjoint from every positive ray $\{p+t u_j:t>0\}$.  Finally, every
--   point of $B(p,\rho)\setminus\{p\}$ which lies on none of the positive rays
--   $\{p+t u_j:t>0\}$ belongs to at least one of the sectors $\Sigma_i$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FinitePlanarClockwiseSuccessorSectors`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePlanarClockwiseSuccessorSectors.lean#L1-L134

import Mathlib.Tactic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma FinitePlanarClockwiseSuccessorSectors {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (p : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (u : ι → EuclideanSpace ℝ (Fin 2))
    (hρ : 0 < ρ)
    (hu : ∀ i : ι, u i ≠ 0)
    (hposRayDistinct :
      ∀ {i j : ι}, (∃ t : ℝ, 0 < t ∧ u j = t • u i) → i = j) :
    ∃ clockwiseNext : Equiv.Perm ι,
      ∃ fullClockwiseTurn : ℝ,
      ∃ clockwiseTurn : ι → ι → ℝ,
      ∃ sector : ι → Set (EuclideanSpace ℝ (Fin 2)),
        fullClockwiseTurn = 2 * Real.pi ∧
        0 < fullClockwiseTurn ∧
        (∀ i j : ι, 0 < clockwiseTurn i j) ∧
        (∀ i j : ι, clockwiseTurn i j ≤ fullClockwiseTurn) ∧
        (∀ i j : ι, clockwiseTurn i j = fullClockwiseTurn ↔ j = i) ∧
        (∀ i j : ι, j ≠ i →
          clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
        (∀ i : ι, clockwiseNext i = i ↔ ∀ j : ι, j = i) ∧
        (∀ i : ι,
          if h : clockwiseNext i = i then
            sector i =
              Metric.ball p ρ \
                ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
                  ({p} : Set (EuclideanSpace ℝ (Fin 2))))
          else
            ∃ c s : ℝ,
              (s ≠ 0 ∨ c < 0) ∧
              u (clockwiseNext i) = c • u i - s • PlanarRot90 (u i) ∧
              sector i =
                (let base : EuclideanSpace ℝ (Fin 2) := u i
                 let baseChart : EuclideanSpace ℝ (Fin 2) →
                    EuclideanSpace ℝ (Fin 2) :=
                  fun z => p + z 0 • base + z 1 • PlanarRot90 base
                 if 0 < s then
                   baseChart ''
                    {z : EuclideanSpace ℝ (Fin 2) |
                      z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                      z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
                 else if s < 0 then
                   baseChart ''
                    {z : EuclideanSpace ℝ (Fin 2) |
                      z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                      (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
                 else
                   baseChart ''
                    {z : EuclideanSpace ℝ (Fin 2) |
                      z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                      z 1 < 0})) ∧
        (∀ i : ι, IsOpen (sector i) ∧ IsConnected (sector i)) ∧
        (∀ i : ι, sector i ⊆ Metric.ball p ρ) ∧
        (∀ i j : ι,
          Disjoint (sector i)
            {q | ∃ t : ℝ, 0 < t ∧ q = p + t • u j}) ∧
        (∀ q : EuclideanSpace ℝ (Fin 2),
          q ∈ Metric.ball p ρ →
            q ≠ p →
              (∀ i : ι,
                q ∉ {x | ∃ t : ℝ, 0 < t ∧ x = p + t • u i}) →
                ∃ i : ι, q ∈ sector i) := by sorry
