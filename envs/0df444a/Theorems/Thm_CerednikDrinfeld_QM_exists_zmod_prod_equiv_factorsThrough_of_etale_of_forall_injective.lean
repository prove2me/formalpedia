-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective
-- name    : CerednikDrinfeld.QM.exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ef265d4f-b2d0-5c9b-81d8-c03b0043a296
-- title:
--   Propagating (ℤ/N)² points to all geometric points
-- statement:
--   Let $R$ be a discrete valuation domain, let $f : \mathcal{A} \to \operatorname{Spec} R$ be a separated morphism, locally of finite type, and let $L$ be a relative group law for $f$: a functorial group structure on the sets $\{\varphi : T \to \mathcal{A} \mid \varphi \text{ followed by } f = t\}$ of sections over each $t : T \to \operatorname{Spec} R$, compatible with base change. Assume $L$ is commutative. Let $N$ be a natural number whose image in $R$ is a unit, and let $\mathrm{lev} : C \to \mathcal{A}$ be a closed immersion such that $\mathrm{lev}$ followed by $f$ is finite and étale. Say a section $P$ over $t$ factors through $\mathrm{lev}$ if $P$ equals $P_0$ followed by $\mathrm{lev}$ for some $P_0 : T \to C$. Assume: the sections factoring through $\mathrm{lev}$ are stable under $L.\mathrm{mul}$ and $L.\mathrm{inv}$; the identity section over every $t$ factors through $\mathrm{lev}$; every section factoring through $\mathrm{lev}$ satisfies $N \cdot P =$ the identity section, where $N \cdot P$ is the $N$-fold iterate $\mathrm{nsmulPt}$ of $L.\mathrm{mul}$ with $P$; the rank of $\mathrm{lev}$ followed by $f$ is $N^2$ at every point of $\operatorname{Spec} R$; and, for every algebraically closed field $k$ and every *injective* ring homomorphism $s_k : R \to k$, there is a bijection $\mathbb{Z}/N \times \mathbb{Z}/N \simeq \{P \text{ over } \operatorname{Spec}(s_k) \mid P \text{ factors through } \mathrm{lev}\}$ carrying $x + y$ to $L.\mathrm{mul}$ of the images of $x$ and $y$. The conclusion is that such a bijection exists for every algebraically closed field $k$ and every ring homomorphism $s_k : R \to k$, injective or not. The proof uses neither the commutativity hypothesis, nor the unit hypothesis on $N$, nor the torsion and rank hypotheses.
--
--   This is the specialisation statement for the finite étale subgroup scheme $C$ of the relative group $\mathcal{A}$ over a discrete valuation ring: the group of geometric points factoring through $C$ has the same shape $(\mathbb{Z}/N)^2$ at every geometric point of $\operatorname{Spec} R$ once it does at the geometric points coming from injective maps (in particular the generic ones). It is used in the construction of level structures on fake elliptic curves, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Mathlib.AlgebraicGeometry.Morphisms.Etale

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (N : ℕ) (hN : IsUnit ((N : ℕ) : R))
    {C : Scheme.{u}} (lev : C ⟶ 𝒜) [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)]
    (lev_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q →
        FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    (lev_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t))
    (lev_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    (lev_rank : ∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2)
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y) := by sorry
