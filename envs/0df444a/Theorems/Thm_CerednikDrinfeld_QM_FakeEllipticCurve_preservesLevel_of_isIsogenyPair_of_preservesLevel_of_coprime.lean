-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isIsogenyPair_of_preservesLevel_of_coprime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isIsogenyPair_of_preservesLevel_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/0642679b-4adf-5a94-88de-28f5f0a0b341
-- title:
--   The quasi-inverse of a level-preserving isogeny preserves the level
-- statement:
--   Fix natural numbers $N, d$, an algebraically closed field $k_0$ in which the image of $N$ is nonzero, with $d$ coprime to $N$, rationals $a, b$, and a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb H[\mathbb Q, a, b]$ that is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb Q$ and is finitely generated. Let $A_0$ be a `FakeEllipticCurve` for $\Lambda$, $N$ over $k_0$ — in particular a scheme $A_0.A$ with structure morphism $A_0.f$ to $\mathrm{Spec}\,k_0$ carrying a commutative relative group law on $T$-points, an action of $\Lambda$ by endomorphisms, and a morphism $A_0.\mathrm{lev}$ out of a scheme $A_0.C$. Let $\varphi, \psi$ be endomorphisms of $A_0.A$ over $\mathrm{Spec}\,k_0$ (so $A_0.f \circ \varphi = A_0.f$ and $A_0.f \circ \psi = A_0.f$) forming an isogeny pair of degree $d$ in the sense of `IsIsogenyPair`: both induce homomorphisms for the group law on $T$-points, both commute with the $\Lambda$-action, and, provided the image of $d$ lies in $\Lambda$ (automatic here, since $\Lambda$ is an order), both composites $\psi \circ \varphi$ and $\varphi \circ \psi$ equal the action of $d$. Assume $\varphi$ preserves the level structure, i.e. for every scheme $T$, every $t : T \to \mathrm{Spec}\,k_0$ and every $T$-point $P$ of $A_0.A$ over $t$, if $P$ factors through $A_0.\mathrm{lev}$ then so does $\varphi \circ P$. The conclusion is the same statement for $\psi$: every $T$-point factoring through $A_0.\mathrm{lev}$ has $\psi \circ P$ again factoring through $A_0.\mathrm{lev}$.
--
--   This is the symmetry statement needed to treat an isogeny pair of degree prime to the level as a pair of level-preserving maps: the quasi-inverse of a level-preserving isogeny of degree coprime to $N$ again preserves the level. It is used in the construction of the dictionary family of fake elliptic curves, namely by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_dictionary_family_of_isPullback_prod_of_forall_mem_awayUnits_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_dictionary_family_of_isPullback_prod_of_forall_mem_awayUnits_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isIsogenyPair_of_preservesLevel_of_coprime.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isIsogenyPair_of_preservesLevel_of_coprime
    {N d : ℕ} (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (hN : (N : k₀) ≠ 0) (hdN : Nat.Coprime d N)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (A₀ : FakeEllipticCurve Λ N k₀)
    (φ ψ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f) (hψ : ψ ≫ A₀.f = A₀.f)
    (hpair : FakeEllipticCurve.IsIsogenyPair d A₀ A₀ φ ψ)
    (hlev : FakeEllipticCurve.PreservesLevel A₀ A₀ φ hφ) :
    FakeEllipticCurve.PreservesLevel A₀ A₀ ψ hψ := by sorry
