-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8405bd8d-19dc-56ed-a0c1-6ee880188eb1
-- title:
--   Level points over injective geometric points form (ℤ/N)²
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$; let $R$ be a commutative ring and $K$ a field which is an $R$-algebra and a fraction field of $R$, and let $E_0$ be a fake elliptic curve of type $(\Lambda,N)$ over $K$, i.e. a scheme $E_0.A$ with a structure morphism $E_0.f$ to $\mathrm{Spec}\,K$, a commutative relative group law $E_0.L$ on the functor of sections, an abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ satisfying the multiplicativity, additivity and trace conditions, and a level morphism $E_0.\mathrm{lev}$ from $E_0.C$ to $E_0.A$. Let $f : \mathcal{A} \to \mathrm{Spec}\,R$ carry a relative group law $L$ (a group structure, natural in the base, on the sections $\{\varphi : T \to \mathcal{A} \mid \varphi \text{ followed by } f = t\}$ for each $t : T \to \mathrm{Spec}\,R$), let $\mathrm{lev} : C \to \mathcal{A}$ be a morphism, and let $g : E_0.A \to \mathcal{A}$ be such that the square formed by $g$, $E_0.f$, $f$ and $\mathrm{Spec}\,K \to \mathrm{Spec}\,R$ is cartesian. Assume further that $g$ is compatible with the group laws: for all $t' : T \to \mathrm{Spec}\,K$ and sections $x,y$ of $E_0.f$ over $t'$, the $E_0.L$-product of $x$ and $y$ followed by $g$ equals the $L$-product, over $t'$ followed by $\mathrm{Spec}\,K \to \mathrm{Spec}\,R$, of $x$ followed by $g$ and $y$ followed by $g$; and that $g$ matches the level data: a section $P$ of $E_0.f$ over $t'$ factors through $E_0.\mathrm{lev}$ if and only if $P$ followed by $g$ factors through $\mathrm{lev}$. The conclusion: for every algebraically closed field $k$ and every injective ring homomorphism $s_k : R \to k$ with $N \neq 0$ in $k$, there is a bijection $e$ from $\mathbb{Z}/N \times \mathbb{Z}/N$ onto the set of those sections $P$ of $f$ over the geometric point $\mathrm{Spec}\,k \to \mathrm{Spec}\,R$ induced by $s_k$ which factor through $\mathrm{lev}$, and $e$ is additive: $e(x+y)$ is the $L$-product of $e(x)$ and $e(y)$ for all $x,y$.
--
--   This transports the assertion that the level structure has $(\mathbb{Z}/N\mathbb{Z})^2$ geometric points from the generic fibre $E_0$ over $K$ to the $R$-model $\mathcal{A}$, at geometric points of $\mathrm{Spec}\,R$ coming from injective maps $R \to k$ (which factor through $K$). It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit) in the construction of integral models of the quaternionic Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_algebraMap_of_injective
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E₀ : FakeEllipticCurve Λ N K)
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {C : Scheme.{u}} (lev : C ⟶ 𝒜)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hg_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t' E₀.f),
      FactorsThrough E₀.lev P ↔ ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.1 ≫ g) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk → (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y) := by sorry
