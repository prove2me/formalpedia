-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/7fb8d2f4-87a2-5303-9181-7e3fff88c5c6
-- title:
--   Fake elliptic curve pull-backs factor through intermediate quotients
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$, and let $B_1 \to B_0$ be a morphism of commutative rings (given as a $B_1$-algebra structure on $B_0$). Let $E$ be a fake elliptic curve for $(\Lambda,N)$ over $B_1$ and $E_0$ one over $B_0$ — in the project's sense: a scheme $A$ over $\operatorname{Spec}$ of the base carrying a commutative relative group law, smooth and proper with connected fibres of dimension $2$, an action of $\Lambda$ by base-preserving endomorphisms that is additive and multiplicative in the group law and satisfies a trace condition on tangent spaces, together with level data $\mathrm{lev} : C \to A$. Let $g : E_0.A \to E.A$ satisfy `IsPullbackVia (algebraMap B₁ B₀) E E₀ g`, that is: the square formed by $g$, $E_0.f$, $E.f$ and $\operatorname{Spec}$ of $B_1 \to B_0$ is a pullback; for every scheme $T$, every $t' : T \to \operatorname{Spec} B_0$ and all $T$-points $P,Q$ of $E_0$ over $t'$, composing their product with $g$ gives the product of $P \circ g$ and $Q \circ g$ as points over $t'$ followed by $\operatorname{Spec}$ of $B_1 \to B_0$; $E_0.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $E.\mathrm{act}\,x$ for all $x \in \Lambda$; and every point factoring through $E_0.\mathrm{lev}$ has its image under $g$ factoring through $E.\mathrm{lev}$. Finally let $K$ be an ideal of $B_1$ every element of which maps to $0$ in $B_0$. Then there exist a fake elliptic curve $E'$ for $(\Lambda,N)$ over $B_1/K$ and morphisms $g_1 : E'.A \to E.A$, $g_0 : E_0.A \to E'.A$ such that $g_1$ exhibits `IsPullbackVia` for the quotient map $B_1 \to B_1/K$, $g_0$ exhibits `IsPullbackVia` for the induced map $B_1/K \to B_0$, and $g_0$ followed by $g_1$ equals $g$.
--
--   This is the single geometric step in a tower argument: it splits a pull-back of fake elliptic curves along $B_1 \to B_0$ into the two legs $B_1 \to B_1/K \to B_0$, with named comparison maps on each leg composing to the given one. It is used in the inductive passage from small-kernel to nilpotent-kernel statements about polarisations and Rosati compatibility on fake elliptic curves over Artinian bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (K : Ideal B₁) (hK : ∀ x ∈ K, algebraMap B₁ B₀ x = 0) :
    ∃ (E' : FakeEllipticCurve Λ N (B₁ ⧸ K)) (g₁ : E'.A ⟶ E.A) (g₀ : E₀.A ⟶ E'.A),
      FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk K) E E' g₁ ∧
      FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.lift K (algebraMap B₁ B₀) hK) E' E₀ g₀ ∧
      g₀ ≫ g₁ = g := by sorry
