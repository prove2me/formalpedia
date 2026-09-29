-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/43f4d2d7-9b8d-5f98-b4d3-3ea149b63ac6
-- title:
--   At most one-dimensional relative cotangent space at a smooth point
-- statement:
--   Let $q$ be a prime and let $O^{\mathrm{nr}}$ be a characteristic-zero discrete valuation domain which is an algebra over $\mathbb{Z}_q$, assumed $(q)$-adically complete with $(q)O^{\mathrm{nr}}$ maximal and with algebraically closed residue field $k$; let $\iota\colon W(\mathbb{F}_{q^2}) \to O^{\mathrm{nr}}$ be a ring homomorphism and let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ for the reduction of $\iota$, that is, a commutative two-dimensional formal group law with a $W(\mathbb{F}_{q^2})$-action and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$, whose Lie algebra is the direct sum of the two invertible eigen-submodules `lieZero` and `lieOne` and whose $[q]$-kernel is finite projective of fibre rank $q^4$. Let $R$ be a Noetherian local $O^{\mathrm{nr}}$-algebra, complete for its maximal ideal, let $\mathrm{res}_R\colon R\to k$ be compatible with the structure map, and let $\mathcal{X}$ be a formal $\mathcal{O}_D$-module over $R$ together with an isomorphism $w_u$ from its reduction along $\mathrm{res}_R$ to $X_0$. Assume $(R,\mathcal{X},w_u)$ pro-represents deformations: for every Artinian local $O^{\mathrm{nr}}$-algebra $A$ with surjective compatible $\mathrm{res}_A\colon A\to k$, every special formal $\mathcal{O}_D$-module $X$ of height $4$ over $A$ and every isomorphism $w$ from the reduction of $X$ to $X_0$, there is a unique $O^{\mathrm{nr}}$-algebra map $\chi\colon R\to A$ over $\mathrm{res}_R$ admitting an isomorphism $v\colon \chi^*\mathcal{X}\cong X$ whose reduction composed with $w$ has the same series as $w_u$. Assume finally that the linear part of $\varpi$ does not annihilate both `lieZero` and `lieOne` of $X_0$. Then there exists $t$ in the maximal ideal of $R$ with $\mathfrak{m}_R = \mathfrak{m}_{O^{\mathrm{nr}}}R + (t) + \mathfrak{m}_R^2$.
--
--   The statement bounds by $1$ the dimension over $k$ of the relative cotangent space $\mathfrak{m}_R/(\mathfrak{m}_{O^{\mathrm{nr}}}R+\mathfrak{m}_R^2)$ of Drinfeld's deformation ring of a special formal $\mathcal{O}_D$-module of height $4$, at a point where exactly one of the two critical indices occurs; dually, first-order deformations of $X_0$ over $k[\varepsilon]$ form a $k$-space of dimension at most one. It feeds the description of $R$ as either a power series ring over $O^{\mathrm{nr}}$ in one variable or the crossing model $O^{\mathrm{nr}}[[u,v]]/(uv-q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ t ∈ IsLocalRing.maximalIdeal R,
      IsLocalRing.maximalIdeal R = (IsLocalRing.maximalIdeal Onr).map (algebraMap Onr R) ⊔ Ideal.span {t} ⊔ (IsLocalRing.maximalIdeal R) ^ 2 := by sorry
