-- Prove2me | Theorems.Thm_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast
-- name    : Algebra.exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d80b0424-952a-57e7-872b-411dc2b33d9f
-- title:
--   Glueing locally defined n-th roots of unity along a Zariski cover
-- statement:
--   Let $A_0$ and $B$ be commutative rings in one and the same universe, with $B$ an $A_0$-algebra, and let $n$ be a natural number whose image in $B$ is a unit. Let $v$ be a rule assigning to every algebraically closed field $\Omega$ equipped with an $A_0$-algebra structure (and in the same universe) and every $A_0$-algebra homomorphism $\varphi : B \to \Omega$ an element $v_\Omega(\varphi) \in \Omega$. Assume $v$ is Zariski-locally given by an $n$-th root of unity, in the following sense: for every prime ideal $\mathfrak p$ of $B$ there exist $f \in B$ with $f \notin \mathfrak p$ and an element $\varepsilon \in B[1/f] =$ `Localization.Away f` with $\varepsilon^n = 1$ such that for every algebraically closed $A_0$-field $\Omega$ and every $A_0$-algebra homomorphism $\phi : B[1/f] \to \Omega$ one has $v_\Omega(\phi \circ (B \to B[1/f])) = \phi(\varepsilon)$, the map $B \to B[1/f]$ being the canonical $A_0$-algebra map. The conclusion is that there exists a single $\varepsilon \in B$ with $\varepsilon^n = 1$ and $v_\Omega(\varphi) = \varphi(\varepsilon)$ for every algebraically closed $A_0$-field $\Omega$ and every $A_0$-algebra homomorphism $\varphi : B \to \Omega$.
--
--   This is the glueing step expressing that a function on geometric points which is locally represented by a section of $\mu_n$, with $n$ invertible, is represented by a global section: the local representatives agree on overlaps because $\mu_n$ is unramified when $n$ is a unit, which here takes the concrete form that a unipotent element of order dividing an invertible $n$ is trivial ([`eq_one_of_isNilpotent_sub_one_of_pow_eq_one`](thm.html#eq_one_of_isNilpotent_sub_one_of_pow_eq_one)). It is applied to the Weil pairing of the two marked points of a level structure, in [`ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ`](thm.html#ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ), to produce a global root of unity on a component of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast
    (A₀ : Type u) [CommRing A₀] (B : Type u) [CommRing B] [Algebra A₀ B] (n : ℕ) (hn : IsUnit ((n : ℕ) : B))
    (v : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω], (B →ₐ[A₀] Ω) → Ω)
    (hloc : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ∃ f : B, f ∉ 𝔭 ∧ ∃ ε : Localization.Away f, ε ^ n = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : Localization.Away f →ₐ[A₀] Ω),
        v Ω (φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away f))) = φ ε) :
    ∃ ε : B, ε ^ n = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : B →ₐ[A₀] Ω), v Ω φ = φ ε := by sorry
