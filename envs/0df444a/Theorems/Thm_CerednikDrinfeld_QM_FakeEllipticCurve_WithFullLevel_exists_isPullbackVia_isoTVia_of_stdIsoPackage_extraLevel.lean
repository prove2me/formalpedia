-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/9c36dea2-3d2c-5cc0-9255-af8ebaa2c0b7
-- title:
--   Unpacking an isomorphism package with extra level after base change
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,m,\ell$, a commutative ring $R$ and a commutative $R$-algebra $L$; write $\iota = \operatorname{Spec}$ of the structure map $R \to L$. Let $u,w$ be objects of `WithFullLevel` $\Lambda$ $N$ $m$ $R$, i.e. fake elliptic curves $u.1,w.1$ over $R$ (abelian schemes of relative dimension $2$ with commutative relative group law, $\Lambda$-action satisfying the trace condition, and level subscheme `lev`) each equipped with a full level-$m$ structure, whose component `P` is a section of the structure morphism over $\operatorname{Spec} R$; let $C_u, C_w$ be `ExtraLevel` $\ell$ data on $u.1$ and $w.1$, that is finite flat closed subschemes $K \hookrightarrow A$ of rank $\ell^2$, of finite presentation, stable under the group law, inversion, the unit, $\Lambda$, killed by $\ell$, disjoint from `lev`, and with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$ where $\ell$ is invertible. Assume given an isomorphism $e$ between the base changes $u.1.f \times \iota$ and $w.1.f \times \iota$ which commutes with the projections to $\operatorname{Spec} L$, is compatible with the base-changed relative group laws on all points, intertwines the base-changed $\Lambda$-actions, carries the base change of $u$'s full-level point to that of $w$'s, and for which the base changes of the level subschemes `lev` correspond in both directions (morphisms $c, c'$ over $e.\mathrm{hom}$ resp. $e.\mathrm{inv}$), and likewise the base changes of $C_u.\mathrm{levK}$ and $C_w.\mathrm{levK}$ in both directions. Then there exist objects $u_L, w_L$ of `WithFullLevel` $\Lambda$ $N$ $m$ $L$, extra level-$\ell$ data $C_{u,L}$ on $u_L.1$ and $C_{w,L}$ on $w_L.1$, and morphisms $g_u : u_L.1.A \to u.1.A$, $g_w : w_L.1.A \to w.1.A$ such that $g_u$ exhibits $u_L.1$ as a base change of $u.1$ along $R \to L$ in the sense of `IsPullbackVia` (the square is a pullback, $g_u$ is compatible with the relative group laws on points, intertwines the $\Lambda$-actions, and sends points factoring through $u_L.1.\mathrm{lev}$ to points factoring through $u.1.\mathrm{lev}$), the full-level point of $u_L$ followed by $g_u$ equals $\iota$ followed by that of $u$, and for every scheme $T_0$ over $\operatorname{Spec} L$ and every point $P$ of $u_L$ over it, $P$ factors through $C_{u,L}.\mathrm{levK}$ if and only if $P$ followed by $g_u$ factors through $C_u.\mathrm{levK}$; the three analogous statements hold for $w_L$, $g_w$, $C_{w,L}$; and finally there is an isomorphism $u_L.1.A \cong w_L.1.A$ over $\operatorname{Spec} L$ satisfying `IsoTVia`, i.e. an isomorphism of the full-level objects $u_L, w_L$ which moreover matches the two extra levels on points.
--
--   This is the unpacking step of the descent of isomorphisms between fake elliptic curves with full and extra level structure: an isomorphism package between the base changes of two triples over an $R$-algebra $L$ is converted into genuine base-changed triples over $L$, presented in the single-morphism `IsPullbackVia` form with extra level the full preimage, together with an isomorphism of triples. It is used in `exists_fg_subalgebra_extraLevel_isPullbackVia_isoTVia_of_isoTVia`, where such an isomorphism is pushed down to a finitely generated subalgebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_mul : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))),
      ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
        ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, e_snd, y.2]⟩).1)
    (e_act : ∀ x : ↥Λ,
      pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ e.hom =
        e.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, w.1.act_over x, pullback.condition]))
    (e_P : pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (u.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ e.hom =
        pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (w.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp]))
    (e_lev : ∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_lev' : ∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv)     (e_levK : ∃ cK : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_levK' : ∃ cK' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK' ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv) :
    ∃ (uL wL : FakeEllipticCurve.WithFullLevel Λ N m L) (CuL : uL.1.ExtraLevel ℓ) (CwL : wL.1.ExtraLevel ℓ)
      (guL : uL.1.A ⟶ u.1.A) (gwL : wL.1.A ⟶ w.1.A),
      FakeEllipticCurve.IsPullbackVia (algebraMap R L) u.1 uL.1 guL ∧
      (uL.2.P).1 ≫ guL = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (u.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' uL.1.f),
        FactorsThrough CuL.levK P ↔ ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ guL) ∧
      FakeEllipticCurve.IsPullbackVia (algebraMap R L) w.1 wL.1 gwL ∧
      (wL.2.P).1 ≫ gwL = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (w.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' wL.1.f),
        FactorsThrough CwL.levK P ↔ ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gwL) ∧
      ∃ (e : uL.1.A ≅ wL.1.A) (he : e.hom ≫ wL.1.f = uL.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia uL wL CuL CwL e he := by sorry
