-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/4f3d6a30-92bc-5ab7-bb36-78c2d9b521d1
-- title:
--   Endomorphism dictionary matches any splitting up to q^{c₀} and conjugation
-- statement:
--   Fix a prime $q$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ and a map $\mathrm{coord}:\Lambda\to \mathbb{Z}_{q^2}\times\mathbb{Z}_{q^2}$ (Witt vectors over $\mathbb{F}_{q^2}$) satisfying `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, has $q$-adically dense image in each coordinate, obeys the twisted multiplication rule $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+q\beta\sigma(\beta'),\,\alpha\beta'+\beta\sigma(\alpha'))$ with $\sigma$ the Witt Frobenius, and matches reduced traces. Let $B$ be a commutative ring in which $q$ is nilpotent, $A_0$ a `FakeEllipticCurve` for $\Lambda$ and level $N$ over $B$, $X_0$ a formal $\mathcal{O}_D$-module of dimension $2$ over $B$ (a commutative law $X_0.F$ with a $\mathbb{Z}_{q^2}$-action and a uniformiser $\varpi$ with $\varpi\circ\varpi=[q]$, $\varpi\circ[a]=[\sigma a]\circ\varpi$), and $\theta_0$ two-dimensional formal coordinates for $A_0.f$ with `IsFormalModuleVia coord X₀ θ₀`: they are formal coordinates for the group law $A_0.L$ with law $X_0.F$, and the action of $m\in\Lambda$ is computed formally by $[\alpha_m]+[\beta_m]\circ\varpi$. Let further $a_1,b_1\in\mathbb{Q}^\times$, let $R_1\subseteq\mathbb{H}[\mathbb{Q},a_1,b_1]$ be an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated), let $c_0\in\mathbb{N}$ and let $e:R_1\to\mathrm{End}(A_0.A)$ assign to each $x$ an endomorphism over $B$ such that: each $e(x)$ is a homomorphism for $A_0.L$ on points over any base, commutes with the $\Lambda$-action, $e(x+y)$ acts on points as the product of $e(x)$ and $e(y)$, $q^{c_0}\cdot e(xy)$ acts as $e(x)\circ e(y)$ whenever $xy\in R_1$, and $e(1)$ acts as multiplication by $q^{c_0}$. Finally let $K_0$ be a field of characteristic zero, $\iota_0:\mathbb{H}[\mathbb{Q},a_1,b_1]\to M_2(K_0)$ any $\mathbb{Q}$-algebra map, and $\mathcal{E}$ any ring homomorphism from the centraliser of all action endomorphisms of $X_0$ together with $\varpi$, inside $\mathrm{End}(X_0.F)$, to $M_2(K_0)$. Then there exists $g\in \mathrm{GL}_2(K_0)$ such that for every $x\in R_1$ and every $u$ in that centraliser whose power series represents $e(x)$ in the coordinates $\theta_0$ (that is, `IsFormalCompletionAlong θ₀ θ₀ (e x) (he x)` holds for `u`), one has $\mathcal{E}(u)=q^{c_0}\,g\,\iota_0(x)\,g^{-1}$.
--
--   This is the compatibility clause linking the supersingular endomorphism dictionary to Drinfeld's description of special formal $\mathcal{O}_D$-modules: a matrix coordinate $\mathcal{E}$ on the $\mathcal{O}_D$-linear endomorphisms of the formal module and an arbitrary splitting $\iota_0$ of the quaternion order at $q$ are shown to agree, for all $x$ simultaneously, up to the factor $q^{c_0}$ and a single conjugation in $\mathrm{GL}_2(K_0)$. It feeds the statement `exists_generalLinearGroup_forall_exists_centralizer_isFormalCompletionAlong_and_apply_eq_zpow_smul_conj`, where the conjugator is absorbed into the ambiguity of the rigidification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong
    {q : ℕ} [Fact q.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) {N : ℕ}

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

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (𝓔 : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀) :
    ∃ g : GL (Fin 2) K₀, ∀ (x : ↥R₁) (u : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
      IsFormalCompletionAlong θ₀ θ₀ (e x) (he x) (MvFormalGroup.Hom.toPowerSeries (u : MvFormalGroup.End X₀.F)) →
        𝓔 u = ((q : K₀) ^ c₀) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
          ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)) := by sorry
