-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_one_of_forall_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/28711061-6da0-5957-bf23-2cd0e6971a3c
-- title:
--   Global function acting as identity on an invertible module is 1
-- statement:
--   Let $T$ be a scheme and let $N$ be a sheaf of modules on $T$ (an object of `T.Modules`) which is invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $T$ there is an open $U \subseteq T$ with $x \in U$ such that the pullback of $N$ along the open immersion $U \hookrightarrow T$ is isomorphic, as a sheaf of modules on $U$, to the unit object, namely the structure sheaf of $U$ viewed as a module over itself. Let $v \in \Gamma(T, \top)$ be a global section of the structure sheaf of $T$, and assume that for every open $U$ of $T$ and every section $s \in \Gamma(N, U)$ the restriction of $v$ along the inclusion $U \le \top$ acts on $s$ as the identity, i.e. $(v|_U) \cdot s = s$. Then $v = 1$ in $\Gamma(T, \top)$.
--
--   This is the standard statement that the structure sheaf acts faithfully, in the global sense, on an invertible module: the hypothesis of invertibility cannot be dropped, since for the zero module every global function acts as the identity. It is used in the comparison of rigidified line bundles on schemes, where it yields the uniqueness of isomorphisms compatible with a given rigidification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_one_of_forall_smul_eq
    {T : Scheme.{u}} {N : T.Modules} (hN : Scheme.Modules.IsInvertible N) (v : Γ(T, ⊤))
    (h : ∀ (U : T.Opens) (s : Γ(N, U)), T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v • s = s) :
    v = 1 := by sorry
