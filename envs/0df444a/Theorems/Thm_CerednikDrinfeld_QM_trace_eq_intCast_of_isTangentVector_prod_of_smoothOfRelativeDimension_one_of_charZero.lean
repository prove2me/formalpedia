-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero
-- name    : CerednikDrinfeld.QM.trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/fdf40c01-c21d-5699-b775-6e2f3bbe795a
-- title:
--   Tangent trace of a matrix quaternion action equals reduced trace
-- statement:
--   Let $k$ be a field of characteristic $0$, $f : A \to \operatorname{Spec} k$ a scheme over $k$ carrying a relative group law $L$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over varying $t : T \to \operatorname{Spec} k$, natural in $T$), assumed commutative, with $f$ smooth of relative dimension $1$. Let $H$ be a ring that is a $\mathbb{Q}$-algebra and $O \subseteq H$ an additive subgroup containing $1$ and closed under multiplication; let $\varepsilon$ assign to each $x \in O$ an endomorphism $\varepsilon(x)$ of $A$ over $\operatorname{Spec} k$ such that post-composition by $\varepsilon(x)$ respects the group law on points, $\varepsilon(1)$ is the identity, $\varepsilon(xy)$ is $\varepsilon(y)$ followed by $\varepsilon(x)$, and post-composition by $\varepsilon(x+y)$ on any point is the $L$-product of the post-compositions by $\varepsilon(x)$ and $\varepsilon(y)$. Let $a, b \in \mathbb{Q}$, $\Lambda$ an additive subgroup of $\mathbb{H}[\mathbb{Q}, a, b]$, and $j : \mathbb{H}[\mathbb{Q}, a, b] \to M_2(H)$ a $\mathbb{Q}$-algebra map with all entries of $j(m)$ in $O$ for $m \in \Lambda$, subject to the following trace condition: for every field $F$ of characteristic $0$ and every $\chi : O \to F$ with $\chi(1) = 1$, $\chi$ additive and $\chi$ multiplicative, and for all $m \in \Lambda$ and $n \in \mathbb{Z}$ with $m + \bar m = n$, one has $\chi(j(m)_{00}) + \chi(j(m)_{11}) = n$ in $F$. Fix $m \in \Lambda$ and an endomorphism $g$ of $A \times_{\operatorname{Spec} k} A$ over $\operatorname{Spec} k$ (over the structure morphism $\operatorname{pr}_1$ followed by $f$) acting on points by the matrix $j(m)$: for every point $P$ of the product, the first component of $g \circ P$ is the $L$-product of $\varepsilon(j(m)_{00})$ applied to the first component and $\varepsilon(j(m)_{01})$ applied to the second, and the second component is the $L$-product of $\varepsilon(j(m)_{10})$ and $\varepsilon(j(m)_{11})$ applied to these components. Let $k'$ be an algebraically closed field with a ring map $sk : k \to k'$, and $V$ a finite-dimensional $k'$-vector space together with an injection $\tau$ of $V$ into the points of $A \times A$ over the dual-number base $\operatorname{Spec} k'[\epsilon] \to \operatorname{Spec} k$ whose image is exactly the tangent vectors of the product group law (those points restricting along $k'[\epsilon] \to k'$ to the unit section at the geometric point $sk$), with $\tau$ additive for the product group law and $k'$-homogeneous via the dual-number scaling maps. Finally let $\Phi : V \to V$ be $k'$-linear with $\tau(\Phi v) = g \circ \tau(v)$ for all $v$, and let $n \in \mathbb{Z}$ satisfy $m + \bar m = n$ in $\mathbb{H}[\mathbb{Q}, a, b]$. Then $\operatorname{tr}_{k'}(\Phi) = n$ in $k'$.
--
--   This is the trace (speciality) condition in the construction of fake elliptic curves: an element of a quaternionic order acting on $A \times A$ through a matrix representation $j$ acts on the tangent space at the origin with trace equal to the reduced trace of the element. It is the characteristic-zero form, with coefficients in an arbitrary $\mathbb{Q}$-algebra, and feeds the verification that the resulting quaternionic action on $A \times A$ satisfies the defining conditions of a fake elliptic curve; the finite-dimensionality input comes from the computation of the tangent space dimension for a smooth relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero
    (k : Type) [Field k] [CharZero k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hLc : L.IsCommutative)
    (hA1 : SmoothOfRelativeDimension 1 f)
    {H : Type} [Ring H] [Algebra ℚ H] (O : Submodule ℤ H) (hO₁ : (1 : H) ∈ O)
    (hOmul : ∀ x y : H, x ∈ O → y ∈ O → x * y ∈ O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : H) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : H) * (y : H) ∈ O),
      ε ⟨(x : H) * (y : H), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) H)
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (hj_trace : ∀ (F : Type) [Field F] [CharZero F] (χ : ↥O → F),
      (∀ h : (1 : H) ∈ O, χ ⟨1, h⟩ = 1) →
      (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
      (∀ (x y : ↥O) (h : (x : H) * (y : H) ∈ O),
        χ ⟨(x : H) * (y : H), h⟩ = χ x * χ y) →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F))
    (m : ↥Λ) (g : pullback f f ⟶ pullback f f) (hg : g ≫ prodStr f f = prodStr f f)
    (hformula : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t (prodStr f f)),
      prodFstPt (pushPt g hg P) =
          L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩) (hε _) (prodFstPt P))
            (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 1, hj m 0 1⟩) (hε _) (prodSndPt P)) ∧
        prodSndPt (pushPt g hg P) =
          L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 0, hj m 1 0⟩) (hε _) (prodFstPt P))
            (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩) (hε _) (prodSndPt P)))
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k')
    (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V]
    (τ : V → SchemeHomOver (tangentBase k' sk) (prodStr f f))
    (hτ_inj : Function.Injective τ)
    (hτ_range : ∀ P : SchemeHomOver (tangentBase k' sk) (prodStr f f),
      P ∈ Set.range τ ↔ IsTangentVector (L.prod L) k' sk P)
    (hτ_add : ∀ v w : V, τ (v + w) = (L.prod L).mul (tangentBase k' sk) (τ v) (τ w))
    (hτ_smul : ∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1)
    (Φ : V →ₗ[k'] V) (hΦ : ∀ v : V, τ (Φ v) = pushPt g hg (τ v))
    (n : ℤ) (hn : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    LinearMap.trace k' V Φ = (n : k') := by sorry
