-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_fibrePower_represents_tuples
-- name    : AlgebraicGeometry.Scheme.exists_fibrePower_represents_tuples
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/9dddb717-123c-5ef1-b49f-8f2bf7736f37
-- title:
--   Representability of n-tuples by the n-fold fibre power
-- statement:
--   Let $B$ and $Y$ be schemes, let $\pi_Y : Y \to B$ be a morphism and let $n$ be a natural number. The assertion is that there exist a scheme $P$, a morphism $\pi_P : P \to B$ and a family of morphisms $q_l : P \to Y$ indexed by $l \in \mathrm{Fin}\,n$ such that: (i) $\pi_Y \circ q_l = \pi_P$ for every $l$; (ii) for every scheme $T$, every $t : T \to B$ and every family $g_l : T \to Y$ ($l \in \mathrm{Fin}\,n$) with $\pi_Y \circ g_l = t$ for all $l$, there is exactly one $G : T \to P$ with $\pi_P \circ G = t$ and $q_l \circ G = g_l$ for all $l$; (iii) if $\pi_Y$ is separated then so is $\pi_P$; (iv) if $\pi_Y$ is locally of finite type then so is $\pi_P$; (v) if $\pi_Y$ is locally of finite presentation then so is $\pi_P$; and (vi) for every family of open subschemes $U_l \subseteq Y$ ($l \in \mathrm{Fin}\,n$) such that each underlying set of $U_l$ is closed in $Y$ and each composite $U_l \hookrightarrow Y \xrightarrow{\pi_Y} B$ is quasi-compact, the open subset $\bigwedge_l q_l^{-1}(U_l)$ of $P$ has closed underlying set and the composite of its inclusion with $\pi_P$ is quasi-compact. Thus $P$ is an $n$-fold fibre power of $Y$ over $B$ together with the stated inheritance of properties.
--
--   This packages the $n$-fold fibre product $Y \times_B \cdots \times_B Y$ over $B$: its universal property, the standard stability of separatedness and of the local finiteness conditions under base change and composition, and the fact that the intersection of the preimages of closed quasi-compact-over-$B$ open pieces is again closed and quasi-compact over $B$. It is used by [`AlgebraicGeometry.exists_tableScheme_of_represents_homScheme`](thm.html#AlgebraicGeometry.exists_tableScheme_of_represents_homScheme) to build the auxiliary scheme parametrising tuples of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_fibrePower_represents_tuples.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_fibrePower_represents_tuples
    {B Y : Scheme.{u}} (πY : Y ⟶ B) (n : ℕ) :
    ∃ (P : Scheme.{u}) (πP : P ⟶ B) (q : Fin n → (P ⟶ Y)),
      (∀ l, q l ≫ πY = πP) ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ B) (g : Fin n → (T ⟶ Y)), (∀ l, g l ≫ πY = t) →
        ∃! G : T ⟶ P, G ≫ πP = t ∧ ∀ l, G ≫ q l = g l) ∧
      (IsSeparated πY → IsSeparated πP) ∧
      (LocallyOfFiniteType πY → LocallyOfFiniteType πP) ∧
      (LocallyOfFinitePresentation πY → LocallyOfFinitePresentation πP) ∧
      (∀ U : Fin n → Y.Opens, (∀ l, IsClosed ((U l : Set Y))) → (∀ l, QuasiCompact ((U l).ι ≫ πY)) →
        IsClosed ((⨅ l, (q l) ⁻¹ᵁ (U l) : P.Opens) : Set P) ∧
        QuasiCompact ((⨅ l, (q l) ⁻¹ᵁ (U l)).ι ≫ πP)) := by sorry
