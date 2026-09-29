-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder
-- name    : CerednikDrinfeld.QM.exists_act_prod_of_algHom_matrix_of_isOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/6af9ba0b-9ac8-5dd5-827f-d6e45f2aefa5
-- title:
--   Matrix representation Λ → M₂(𝒪) acting on A ×_R A
-- statement:
--   Fix a commutative ring $R$ and a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} R$, and let $L$ be a relative group law for $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f\text{-compatible}\}$ of $T$-points over $\operatorname{Spec} R$, natural in $T$) which is commutative. Let $O \subseteq \mathbb H[\mathbb Q,c,d]$ be a $\mathbb Z$-submodule which is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb Q$ and is finitely generated. Suppose given $\varepsilon$ assigning to each $x \in O$ an endomorphism $\varepsilon x$ of $A$ over $\operatorname{Spec} R$ ($\varepsilon x$ followed by $f$ equals $f$) such that each $\varepsilon x$ acts on $T$-points as a homomorphism for $L$, $\varepsilon 1 = \mathrm{id}_A$ whenever $1 \in O$, $\varepsilon(xy) = \varepsilon y$ followed by $\varepsilon x$ whenever $xy \in O$, and $\varepsilon(x+y)$ acts on points as the $L$-product of the actions of $\varepsilon x$ and $\varepsilon y$. Let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule, $j : \mathbb H[\mathbb Q,a,b] \to M_2(\mathbb H[\mathbb Q,c,d])$ a $\mathbb Q$-algebra homomorphism with all entries $j(m)_{il}$ lying in $O$ for $m \in \Lambda$. The conclusion asserts the existence of a family $\mathrm{act}(m)$, $m \in \Lambda$, of endomorphisms of the fibre product $A \times_{\operatorname{Spec} R} A$ over $\operatorname{Spec} R$ such that: for every $T$-point $P$ of the product, the first component of $\mathrm{act}(m) \circ P$ is the $L$-product of $\varepsilon(j(m)_{00})$ applied to the first component of $P$ and $\varepsilon(j(m)_{01})$ applied to its second component, and the second component is the $L$-product of $\varepsilon(j(m)_{10})$ on the first component and $\varepsilon(j(m)_{11})$ on the second; each $\mathrm{act}(m)$ is a homomorphism for the product group law $L \times L$ on $T$-points; $\mathrm{act}(1) = \mathrm{id}$ when $1 \in \Lambda$; $\mathrm{act}(xy)$ equals $\mathrm{act}(y)$ followed by $\mathrm{act}(x)$ whenever $xy \in \Lambda$; and $\mathrm{act}(x+y)$ acts on points as the $(L \times L)$-product of the actions of $\mathrm{act}(x)$ and $\mathrm{act}(y)$.
--
--   This is the classical embedding $M_2(\operatorname{End} A) \hookrightarrow \operatorname{End}(A \times A)$ for a commutative group object, transcribed into the functor-of-points vocabulary: an integral two-by-two matrix representation of $\Lambda$ over an order $O$ acting on $A$ produces an action of $\Lambda$ on $A \times_R A$. It is used in the construction of quaternionic (fake elliptic curve) moduli data, being cited in the production of a fake elliptic curve from a matrix representation together with a trace condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.lean

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

theorem CerednikDrinfeld.QM.exists_act_prod_of_algHom_matrix_of_isOrder
    {R : Type} [CommRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) (hLc : L.IsCommutative)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O) :
    ∃ (act : ↥Λ → (pullback f f ⟶ pullback f f)) (hact : ∀ m : ↥Λ, act m ≫ prodStr f f = prodStr f f),
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        prodFstPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 1, hj m 0 1⟩) (hε _) (prodSndPt P)) ∧
          prodSndPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 0, hj m 1 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩) (hε _) (prodSndPt P))) ∧
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (prodStr f f)),
        pushPt (act m) (hact m) ((L.prod L).mul t P Q) =
          (L.prod L).mul t (pushPt (act m) (hact m) P) (pushPt (act m) (hact m) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 (pullback f f)) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        pushPt (act (x + y)) (hact (x + y)) P =
          (L.prod L).mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P)) := by sorry
