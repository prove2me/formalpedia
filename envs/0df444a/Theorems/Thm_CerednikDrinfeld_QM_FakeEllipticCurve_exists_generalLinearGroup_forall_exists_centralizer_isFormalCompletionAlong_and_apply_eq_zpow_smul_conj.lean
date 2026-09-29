-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/cfe08ecd-bdd6-5cd1-93f2-a4873b2a836e
-- title:
--   Formal completions of q-power quasi-endomorphisms in matrix coordinates
-- statement:
--   Fix a prime $q$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ containing the image of every rational integer, and let $\mathrm{coord}:\Lambda\to\mathbb{Z}_{q^2}\times\mathbb{Z}_{q^2}$ (values in the Witt vectors of $\mathbb{F}_{q^2}$) satisfy `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is multiplicative for the Frobenius-twisted rule $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+q\beta\sigma(\beta'),\alpha\beta'+\beta\sigma(\alpha'))$, is injective, has dense image modulo every power of $q$, and matches reduced traces. Let $B$ be a commutative ring with $q$ nilpotent, $A_0$ a fake elliptic curve over $B$ of level $N$ with $\Lambda$-action, $X_0$ a two-dimensional formal $\mathcal{O}_D$-module over $B$ (a formal group law with $\mathbb{Z}_{q^2}$-action and uniformiser series $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$), and $\theta_0$ formal coordinates of dimension $2$ on $A_0.f$ exhibiting $X_0$ as the formal $\mathcal{O}_D$-module of $A_0$ via $\mathrm{coord}$. Let $a_1,b_1\in\mathbb{Q}^{\times}$, let $R_1\subseteq\mathbb{H}[\mathbb{Q},a_1,b_1]$ be an order (containing $1$, multiplicatively closed, spanning over $\mathbb{Q}$, finitely generated), let $c_0\in\mathbb{N}$ and let $e:R_1\to\mathrm{End}(A_0.A)$ take values in endomorphisms over $B$ which are homomorphisms for the relative group law on points over every base, commute with the $\Lambda$-action, are additive in the argument on points, satisfy $[q^{c_0}]\circ e(xy)=e(x)\circ e(y)$ whenever $xy\in R_1$, and $e(1)=[q^{c_0}]$ on points. Let $I$ be a type, $w:I\to\mathbb{H}[\mathbb{Q},a_1,b_1]$ and $e_I:I\to\mathrm{End}(A_0.A)$ endomorphisms over $B$ that are again homomorphisms on points and commute with the $\Lambda$-action, such that for each $i$ there are $k,j\in\mathbb{N}$ and $x\in R_1$ with $x=q^{k}w(i)$ and $e_I(i)$ followed by the action of $q^{j}\in\Lambda$ equal to $e(x)$. Finally let $K_0$ be a field of characteristic zero, $\iota_0$ a $\mathbb{Q}$-algebra homomorphism $\mathbb{H}[\mathbb{Q},a_1,b_1]\to M_2(K_0)$, and $\mathcal{E}$ a ring homomorphism from the centralizer of $\{\mathrm{actEnd}(a)\}_{a}\cup\{\varpi\}$ in $\mathrm{End}(X_0.F)$ to $M_2(K_0)$. Then there is $g\in\mathrm{GL}_2(K_0)$ such that for every $i\in I$ there are an element $\varepsilon$ of that centralizer and $k_i\in\mathbb{Z}$ with: the power series of $\varepsilon$ is the formal completion of $e_I(i)$ along $\theta_0$, i.e. for every $B$-algebra $B'$, ideal $J$ with $J^{n+1}=0$ and $s$ with entries in $J$ one has $\theta_0(\mathrm{nilEval}\,\varepsilon(s))=e_I(i)\circ\theta_0(s)$, and $\mathcal{E}(\varepsilon)=q^{k_i}\,g\,\iota_0(w(i))\,g^{-1}$.
--
--   This is the compatibility, at a point of the moduli problem with nilpotent $q$, between quasi-endomorphisms of a fake elliptic curve given by $q$-power multiples of elements of a quaternion order and their formal completions on the associated formal $\mathcal{O}_D$-module, expressed in a single matrix coordinate system: one conjugating matrix $g$ works simultaneously for the whole family indexed by $I$, the scaling being absorbed into an integral power of $q$. It is the form of the Čerednik–Drinfeld endomorphism dictionary consumed by the construction of the action on the Bruhat–Tits tree by away-from-$q$ units, and it is used by the downstream statement producing an order and a maximal order intersection from such an action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion MatrixGroups

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj
    {q : ℕ} [Fact q.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (q : B))

    (A₀ : FakeEllipticCurve Λ N B) (X₀ : FormalODModule q B) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hθ₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    {a₁ b₁ : ℚ} (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁)
    (c₀ : ℕ) (e : ↥R₁ → (A₀.A ⟶ A₀.A)) (he : ∀ x : ↥R₁, e x ≫ A₀.f = A₀.f)
    (hhom : ∀ (x : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (e x) (he x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e x) (he x) Q))
    (hlin : ∀ (x : ↥R₁) (m : ↥Λ), A₀.act m ≫ e x = e x ≫ A₀.act m)
    (hadd : ∀ (x y : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e (x + y)) (he (x + y)) P = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e y) (he y) P))
    (hmul : ∀ (x y : ↥R₁) (hxy : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₁)
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      nsmulPt A₀.L t (q ^ c₀) (pushPt (e ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩) (he _) P) =
        pushPt (e x) (he x) (pushPt (e y) (he y) P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e ⟨1, hR₁.one_mem⟩) (he _) P = nsmulPt A₀.L t (q ^ c₀) P)

    {I : Type} (w : I → ℍ[ℚ, a₁, b₁]) (eI : I → (A₀.A ⟶ A₀.A)) (heI : ∀ i : I, eI i ≫ A₀.f = A₀.f)
    (heIhom : ∀ (i : I) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (eI i) (heI i) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (eI i) (heI i) P) (pushPt (eI i) (heI i) Q))
    (heIlin : ∀ (i : I) (m : ↥Λ), A₀.act m ≫ eI i = eI i ≫ A₀.act m)
    (hI : ∀ i : I, ∃ (k j : ℕ) (x : ↥R₁), (x : ℍ[ℚ, a₁, b₁]) = ((q ^ k : ℕ) : ℚ) • w i ∧
      eI i ≫ A₀.act ⟨(((q ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e x)

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (𝓔 : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀) :
    ∃ g : GL (Fin 2) K₀, ∀ i : I,
      ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (ki : ℤ),
        IsFormalCompletionAlong θ₀ θ₀ (eI i) (heI i) (MvFormalGroup.Hom.toPowerSeries (ε : MvFormalGroup.End X₀.F)) ∧
        𝓔 ε = ((q : K₀) ^ ki) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (w i) *
          ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)) := by sorry
