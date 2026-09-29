-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/d72c950e-0db6-5982-b733-c361a4e75187
-- title:
--   Descent of extra-level isomorphism packages to finitely generated subalgebras
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ subject to `IsMaximalOrder Λ`, i.e. $\Lambda$ is an order and every order containing it coincides with it. Fix natural numbers $N$, $m$, $\ell$, a Noetherian commutative ring $R$ and a commutative $R$-algebra $L$ (both in the bottom universe). Let $u$ and $w$ be elements of `FakeEllipticCurve.WithFullLevel Λ N m R`, that is, dependent pairs whose first component $u.1$ is a fake elliptic curve over $R$ with level $N$ — a scheme $A$ with structure morphism $f : A \to \operatorname{Spec} R$, a commutative relative group law $u.1.L$ on $f$, an abelian-scheme property bundle, two-dimensional fibres, an action $\mathrm{act}$ of $\Lambda$ by endomorphisms of $A$ over $\operatorname{Spec} R$ which is additive and multiplicative, compatible with the group law and has the prescribed reduced traces, and a level subscheme $\mathrm{lev} : C \to A$ — and whose second component $u.2$ is a full level-$m$ structure on $u.1$; the component $u.2.P$ used below is a section of $u.1.f$ over $\operatorname{Spec} R$.
--
--   Let $C_u$ be an `ExtraLevel ℓ` structure on $u.1$ and $C_w$ one on $w.1$: a scheme $K$ together with a closed immersion $\mathrm{levK} : K \to A$ such that the points factoring through $\mathrm{levK}$ are closed under the group law and inversion, contain the identity section, are killed by $\ell$, are stable under every $\mathrm{act}\,x$ ($x \in \Lambda$) and meet the points factoring through $\mathrm{lev}$ only in the identity, while $\mathrm{levK} \circ f$ ($\mathrm{levK}$ followed by $f$) is finite, flat and locally of finite presentation of fibre rank $\ell^2$, with geometric fibres isomorphic as groups to $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ whenever $\ell$ is invertible in the algebraically closed field of the geometric point.
--
--   Write $\iota =$ `Spec.map (CommRingCat.ofHom (algebraMap R L))`. The data over $L$ consist of an isomorphism $e : \mathrm{pullback}\,(u.1.f)\,\iota \;\cong\; \mathrm{pullback}\,(w.1.f)\,\iota$ subject to the following clauses, which together form the standard isomorphism package with extra level:
--
--   `e_snd`: $e.\mathrm{hom}$ followed by the second projection of the pullback for $w$ equals the second projection for $u$, so $e$ is an isomorphism over $\operatorname{Spec} L$;
--
--   `e_mul`: for every scheme $T'$, every morphism $t : T' \to \operatorname{Spec} L$ and all $T'$-points $x,y$ over $t$ of the base change of $u.1.A$ (i.e. morphisms to the pullback commuting with $t$ and the second projection), the underlying morphism of the product of $x$ and $y$ for the base-changed group law `u.1.L.baseChange ι`, followed by $e.\mathrm{hom}$, equals the underlying morphism of the product, for `w.1.L.baseChange ι`, of the transported points $x$ followed by $e.\mathrm{hom}$ and $y$ followed by $e.\mathrm{hom}$;
--
--   `e_act`: for each $x \in \Lambda$, the endomorphism of $\mathrm{pullback}\,(u.1.f)\,\iota$ induced by $u.1.\mathrm{act}\,x$ on the first factor and the identity on the base, followed by $e.\mathrm{hom}$, equals $e.\mathrm{hom}$ followed by the endomorphism of $\mathrm{pullback}\,(w.1.f)\,\iota$ induced by $w.1.\mathrm{act}\,x$;
--
--   `e_P`: the $L$-point of $\mathrm{pullback}\,(u.1.f)\,\iota$ obtained from $\iota$ followed by $u.2.P$ on the first factor and the identity on the base, followed by $e.\mathrm{hom}$, equals the corresponding $L$-point built from $w.2.P$;
--
--   `e_lev` and `e_lev'`: there exists a morphism $c$ from $\mathrm{pullback}\,(u.1.\mathrm{lev} \circ u.1.f)\,\iota$ to $\mathrm{pullback}\,(w.1.\mathrm{lev} \circ w.1.f)\,\iota$ (compositions in diagrammatic order) such that $c$ followed by the canonical morphism $\mathrm{pullback}\,(w.1.\mathrm{lev} \circ w.1.f)\,\iota \to \mathrm{pullback}\,(w.1.f)\,\iota$ induced by $w.1.\mathrm{lev}$ equals the canonical morphism for $u$ followed by $e.\mathrm{hom}$; and, symmetrically, a morphism $c'$ in the opposite direction with the canonical morphism for $u$ as target, matching the canonical morphism for $w$ followed by $e.\mathrm{inv}$;
--
--   `e_levK` and `e_levK'`: the same two one-sided conditions with $u.1.\mathrm{lev}$ and $w.1.\mathrm{lev}$ replaced by the extra-level immersions $C_u.\mathrm{levK}$ and $C_w.\mathrm{levK}$, giving morphisms $c_K$ and $c_K'$.
--
--   Finally, let $s$ be a finite subset of $L$.
--
--   The conclusion asserts the existence of an $R$-subalgebra $T$ of $L$ such that $T$ is finitely generated, the underlying set of $s$ is contained in $T$, and, writing $\iota_T =$ `Spec.map (CommRingCat.ofHom (algebraMap R ↥T))`, there exist an isomorphism $e_T : \mathrm{pullback}\,(u.1.f)\,\iota_T \cong \mathrm{pullback}\,(w.1.f)\,\iota_T$ and a proof $e_T{}_{\mathrm{snd}}$ that $e_T.\mathrm{hom}$ followed by the second projection for $w$ equals the second projection for $u$ (this equality is bound as data, since it is needed to state the next clause), for which all of the following hold: the multiplicativity clause for $e_T$ with respect to the group laws `u.1.L.baseChange ι_T` and `w.1.L.baseChange ι_T`, in exactly the form of `e_mul` with $T$ in place of $L$; the equivariance clause for every $x \in \Lambda$, in the form of `e_act`; the compatibility with the points $u.2.P$ and $w.2.P$, in the form of `e_P`; the existence of a morphism $c$ between the pullbacks of $u.1.\mathrm{lev} \circ u.1.f$ and $w.1.\mathrm{lev} \circ w.1.f$ along $\iota_T$ satisfying the analogue of `e_lev` for $e_T.\mathrm{hom}$; the existence of a morphism $c'$ in the opposite direction satisfying the analogue of `e_lev'` for $e_T.\mathrm{inv}$; and the two corresponding statements for the extra-level immersions, namely a morphism $c_K$ satisfying the analogue of `e_levK` for $e_T.\mathrm{hom}$ and a morphism $c_K'$ satisfying the analogue of `e_levK'` for $e_T.\mathrm{inv}$.
--
--   The statement records only the existence of the descended package over a finitely generated stage; unlike the finite-presentation lemmas it invokes, it asserts no compatibility between $e_T$ and the original isomorphism $e$ over $L$.
--
--   This is the descent step of a limit argument in the style of EGA IV 8.8: an isomorphism between two base-changed fake elliptic curves with level and extra-level data, defined over an arbitrary $R$-algebra $L$, already exists over a finitely generated — hence Noetherian — $R$-subalgebra containing any prescribed finite set of elements. It is used in the Čerednik–Drinfeld part of the development, where statements about moduli of fake elliptic curves with level structure over a general base are reduced to finite-type bases; it is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_extraLevel_isPullbackVia_isoTVia_of_isoTVia`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_extraLevel_isPullbackVia_isoTVia_of_isoTVia).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m ℓ : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
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
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv)
    (e_levK : ∃ cK : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_levK' : ∃ cK' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK' ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv)
    (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (eT : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (eT_snd : eT.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))),
        (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))),
          ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))).mul t x y).1 ≫ eT.hom =
            ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))).mul t
              ⟨x.1 ≫ eT.hom, by rw [Category.assoc, eT_snd, x.2]⟩ ⟨y.1 ≫ eT.hom, by rw [Category.assoc, eT_snd, y.2]⟩).1) ∧
        (∀ x : ↥Λ,
          pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
              (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ eT.hom =
            eT.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
              (by rw [Category.assoc, w.1.act_over x, pullback.condition])) ∧
        (pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ (u.2.P).1) (𝟙 _)
              (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ eT.hom =
            pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ (w.2.P).1) (𝟙 _)
              (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp])) ∧
        (∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.hom) ∧
        (∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.inv) ∧
        (∃ cK : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            cK ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.hom) ∧
        (∃ cK' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            cK' ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.inv) := by sorry
