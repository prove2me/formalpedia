-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
-- name    : AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/328b8164-5d9b-50c9-8293-5ef7007bb3ac
-- title:
--   Splitting an adelic maximal compact element at and away from S
-- statement:
--   Let $F$ be a number field, $S$ a finite set of height-one primes of $\mathcal{O}_F$, and $k$ an element of $\mathrm{GL}_2$ of the adele ring of $F$ (the type `AdelicGL2 (𝓞 F) F`) lying in `adelicMaximalCompact F`, that is: the finite part `glFin` of $k$ lies in `finiteIntegralGL2`, the level-zero group at the unit ideal, and for each infinite place $w$ the component at $w$ of the archimedean part `glArch` of $k$ satisfies `IsRowIsometry`, i.e. its determinant has norm $1$ and the map $(x,y)\mapsto (x,y)$ times the matrix preserves $\|x\|^2+\|y\|^2$. The conclusion asserts the existence of $k_1,k_2$ in the same group with $k = k_1 k_2$, where $k_1$ lies in `maximalCompactAt F S`, namely in `adelicMaximalCompact F` and with finite component at $v$ equal to $1$ for every prime $v \notin S$, and $k_2$ lies in `maximalCompactAway F S`, namely in `adelicMaximalCompact F`, with trivial archimedean part `glArch`, and with finite component at $v$ equal to $1$ for every $v \in S$. Only existence of the factorisation is asserted, with no uniqueness or continuity claim.
--
--   This is the component surgery that splits the maximal compact subgroup of $\mathrm{GL}_2$ over the adeles of $F$ into its part supported at a finite set $S$ of finite places together with the archimedean places, and its part supported at the finite places outside $S$. It is used in the Rankin–Selberg and intertwining-integral estimates of the project, where a compact group element must be moved past data that is local at $S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F, k₁ ∈ maximalCompactAt F S ∧ k₂ ∈ maximalCompactAway F S ∧ k = k₁ * k₂ := by sorry
