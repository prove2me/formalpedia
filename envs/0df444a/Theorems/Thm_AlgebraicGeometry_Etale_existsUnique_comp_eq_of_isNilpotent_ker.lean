-- Prove2me | Theorems.Thm_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker
-- name    : AlgebraicGeometry.Etale.existsUnique_comp_eq_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f873074e-a9db-5b21-8004-a115a588fcd8
-- title:
--   Unique infinitesimal lifting along étale morphisms
-- statement:
--   Let $X$, $Y$, $T$ and $T_0$ be schemes, let $q : Y \to X$ be étale, and let $k : T_0 \to T$ be a closed immersion whose associated ideal, the kernel `k.ker` of the corresponding surjection of structure sheaves, is nilpotent. Suppose given a morphism $t : T \to X$ and a morphism $s_0 : T_0 \to Y$ which agree over $X$ in the sense that $s_0$ followed by $q$ equals $k$ followed by $t$. Then there is exactly one morphism $s : T \to Y$ such that $s$ followed by $q$ equals $t$ and $k$ followed by $s$ equals $s_0$; that is, the commutative square formed by $k$, $q$, $t$ and $s_0$ admits a unique diagonal filler $s$ which is simultaneously a lift of $t$ along $q$ and an extension of $s_0$ along $k$. No affineness, separatedness, finiteness or quasi-compactness hypotheses are imposed on any of the four schemes; they are arbitrary schemes in the lowest universe.
--
--   This is the unique infinitesimal lifting property characterising étale morphisms: an étale morphism is formally étale, so lifts along nilpotent thickenings exist and are unique. It is used in the construction of étale neighbourhoods with the corresponding lifting property, via [`AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent`](thm.html#AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Etale.existsUnique_comp_eq_of_isNilpotent_ker
    {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X) [Etale q] (k : T₀ ⟶ T) [IsClosedImmersion k] (hk : IsNilpotent k.ker)
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by sorry
