-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_one_mem_of_mul_mem
-- name    : CerednikDrinfeld.QM.exists_act_prod_of_algHom_matrix_of_one_mem_of_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/8741f83a-e71b-5bc1-b7c7-5508323402b4
-- title:
--   Matrix action of a lattice on A×_R A through j
-- statement:
--   Let $R$ be a commutative ring, $f : A \to \operatorname{Spec} R$ a scheme over $\operatorname{Spec} R$, and $L$ a relative group law on $f$ (a functorial group structure $L.\mathrm{mul}, L.\mathrm{one}, L.\mathrm{inv}$ on the sets $\mathrm{SchemeHomOver}\,t\,f$ of $T$-points $\varphi : T \to A$ with $\varphi \circ f = t$, for all $t : T \to \operatorname{Spec} R$, natural in $T$) which is commutative. Let $H$ be a ring that is a $\mathbb Q$-algebra, $O \subseteq H$ an additive subgroup (a $\mathbb Z$-submodule) containing $1$ and closed under multiplication, and $\varepsilon$ an assignment to each $x \in O$ of an endomorphism $\varepsilon x : A \to A$ over $\operatorname{Spec} R$ (i.e. $\varepsilon x$ followed by $f$ is $f$) such that: composing a $T$-point with $\varepsilon x$ is a homomorphism for $L.\mathrm{mul}$; $\varepsilon 1 = \mathbb 1_A$; $\varepsilon(xy)$ is $\varepsilon y$ followed by $\varepsilon x$; and on every $T$-point $P$, the point pushed by $\varepsilon(x+y)$ is the $L$-product of the points pushed by $\varepsilon x$ and by $\varepsilon y$. Let $a, b \in \mathbb Q$, let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q, a, b]$, and let $j : \mathbb H[\mathbb Q, a, b] \to M_2(H)$ be a $\mathbb Q$-algebra homomorphism with all four entries $j(m)_{il}$ lying in $O$ for every $m \in \Lambda$. Then there exist a map $\mathrm{act}$ sending each $m \in \Lambda$ to an endomorphism of $\mathrm{pullback}\,f\,f$ over $\operatorname{Spec} R$ (compatible with the structure morphism $\mathrm{prodStr}\,f\,f = \mathrm{pullback.fst}\,f\,f$ followed by $f$) such that, for every $T$-point $P$ of $\mathrm{prodStr}\,f\,f$, the two components of $P$ pushed by $\mathrm{act}\,m$ are the $L$-products $\varepsilon(j(m)_{00})_*\mathrm{pr}_1 P \cdot \varepsilon(j(m)_{01})_*\mathrm{pr}_2 P$ and $\varepsilon(j(m)_{10})_*\mathrm{pr}_1 P \cdot \varepsilon(j(m)_{11})_*\mathrm{pr}_2 P$ respectively; moreover each $\mathrm{act}\,m$ is a homomorphism for the product group law $L.\mathrm{prod}\,L$ on $\mathrm{pullback}\,f\,f$, $\mathrm{act}\,1 = \mathbb 1$ whenever $1 \in \Lambda$, $\mathrm{act}(xy)$ is $\mathrm{act}\,y$ followed by $\mathrm{act}\,x$ for $x, y \in \Lambda$ with $xy \in \Lambda$, and $\mathrm{act}(x+y)$ pushes each point to the $L.\mathrm{prod}\,L$-product of its pushes by $\mathrm{act}\,x$ and $\mathrm{act}\,y$.
--
--   This is the classical inclusion $M_2(\operatorname{End} A) \subseteq \operatorname{End}(A \times_R A)$ for a commutative relative group object, written in the functor-of-points language: a matrix representation $j$ of a rational quaternion algebra with entries in the coefficient ring $O$ acting on $A$ produces an action of the lattice $\Lambda$ on $A \times_R A$. It feeds the construction of fake elliptic curves over a base, being cited by [`CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_one_of_act_of_algHom_matrix_of_trace_of_charZero`](thm.html#CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_one_of_act_of_algHom_matrix_of_trace_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_one_mem_of_mul_mem.lean

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

theorem CerednikDrinfeld.QM.exists_act_prod_of_algHom_matrix_of_one_mem_of_mul_mem
    {R : Type} [CommRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) (hLc : L.IsCommutative)
    {H : Type} [Ring H] [Algebra ℚ H] (O : Submodule ℤ H) (hO₁ : (1 : H) ∈ O)
    (hOmul : ∀ x y : H, x ∈ O → y ∈ O → x * y ∈ O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : H) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : H) * (y : H) ∈ O),
      ε ⟨(x : H) * (y : H), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) H)
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
