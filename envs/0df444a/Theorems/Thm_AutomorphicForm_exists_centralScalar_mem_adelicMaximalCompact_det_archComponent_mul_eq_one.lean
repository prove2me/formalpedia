-- Prove2me | Theorems.Thm_AutomorphicForm_exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one
-- name    : AutomorphicForm.exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/54ab33a8-1f60-517e-a477-2dd76340f1d5
-- title:
--   Central idele correction making all archimedean determinants one
-- statement:
--   Let $F$ be a number field and let $k$ be an element of $\mathrm{GL}_2$ over the adele ring of $F$ lying in `adelicMaximalCompact F`, i.e. its finite part `glFin` lies in `finiteIntegralGL2` (the full-level subgroup `finiteLevelZero` at the ideal $\top$) and, at every infinite place $w$, its component `archComponent F w (glArch … k)` in $\mathrm{GL}_2(F_w)$ satisfies `IsRowIsometry`: the determinant has norm $1$ and for all $x,y \in F_w$ one has $\|x k_{00}+y k_{10}\|^2+\|x k_{01}+y k_{11}\|^2=\|x\|^2+\|y\|^2$. Assume moreover that at every real place $w$ the determinant of the component of $k$ at $w$ is exactly $1$. The conclusion is the existence of a unit $z$ of the adele ring of $F$ such that the central scalar matrix `centralScalar` applied to $z$ (the diagonal $\mathrm{GL}_2$-element with entries $z$) again lies in `adelicMaximalCompact F`, has determinant $1$ at every real place, and such that the product $k \cdot \mathrm{centralScalar}(z)$ has determinant exactly $1$ at *every* infinite place of $F$, real or complex.
--
--   This is the $U(2)=SU(2)\cdot U(1)$ splitting step for the standard maximal compact subgroup of $\mathrm{GL}_2$ of the adeles: an element of the maximal compact whose determinant is $1$ at the real places can be corrected by a central idele, unitary at the infinite places and trivial at the finite places, so as to have determinant $1$ at all infinite places. It is used in the construction of a finite-dimensional bi-invariant subspace of automorphic forms, where the correcting central element is absorbed by a central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (hreal : ∀ w : InfinitePlace F, w.IsReal →
      ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ,
      centralScalar (𝓞 F) F z ∈ adelicMaximalCompact F ∧
      (∀ w : InfinitePlace F, w.IsReal →
        ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) ∧
      (∀ w : InfinitePlace F,
        ((archComponent F w (glArch (𝓞 F) F (k * centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) := by sorry
