-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_ringEquiv_of_ringEquiv_apply_eq
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_ringEquiv_of_ringEquiv_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/fb532394-df52-5a59-b9ba-c8f9fc5f84cc
-- title:
--   Frame isomorphisms induce isomorphisms of two-chart integral models
-- statement:
--   Let $R,R'$ be commutative rings and $F,F'$ fields, with $F$ an $R$-algebra and $F'$ an $R'$-algebra, and let $j\in F$, $j'\in F'$ be non-zero. Suppose given ring isomorphisms $e_0:R\simeq R'$ and $e:F\simeq F'$ such that $e(\mathrm{alg}_{R\to F}(r))=\mathrm{alg}_{R'\to F'}(e_0 r)$ for all $r\in R$, and $e(j)=j'$. Recall that `chartAlgFin R F j` is the subalgebra of $F$ of elements integral over $R[j]=\mathrm{Algebra.adjoin}\,R\,\{j\}$, `chartAlgInf R F j` is the subalgebra of elements integral over $R[j^{-1}]$, and [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two morphisms $\mathrm{Spec}$ applied to the inclusions `inclFin`, `inclInf` of these chart algebras into the overlap algebra, with `toBase R F j` the induced morphism to $\mathrm{Spec}\,R$ determined by the two structure maps $R\to$ `chartAlgFin`, $R\to$ `chartAlgInf`. The assertion is that there exist an isomorphism of schemes $w$ between the two models, and ring isomorphisms $e_{\mathrm{Fin}}$ of the finite chart algebras and $e_{\mathrm{Inf}}$ of the pole chart algebras, such that $e_{\mathrm{Fin}}$ and $e_{\mathrm{Inf}}$ are restrictions of $e$ (their values agree with $e$ after the coercions into $F'$), such that $w$ followed by `toBase R' F' j'` equals `toBase R F j` followed by $\mathrm{Spec}(e_0^{-1})$, and such that for both charts $\mathrm{Spec}(e_{\bullet})$ followed by the structural morphism `ιFin`/`ιInf` of the first model equals the corresponding structural morphism of the second model followed by $w^{-1}$.
--
--   This is the functoriality of the two-chart integral model in isomorphisms of the whole frame — base ring, field and chosen parameter — simultaneously, refining the case of a fixed base; the chart algebras, being integral closures of $R[j^{\pm1}]$ in $F$, are carried onto those of $R'[j'^{\pm1}]$ in $F'$, and the gluing is transported accordingly. It is used to move scheme-level statements, such as the existence of smooth open neighbourhoods of good points, between models attached to different but isomorphic frames in the descent arguments for the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_ringEquiv_of_ringEquiv_apply_eq.lean

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_ringEquiv_of_ringEquiv_apply_eq
    (R R' : Type u) [CommRing R] [CommRing R'] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R' F']
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (e₀ : R ≃+* R') (e : F ≃+* F')
    (he₀ : ∀ r : R, e (algebraMap R F r) = algebraMap R' F' (e₀ r)) (he : e j = j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R' F' j')
      (eFin : chartAlgFin R F j ≃+* chartAlgFin R' F' j') (eInf : chartAlgInf R F j ≃+* chartAlgInf R' F' j'),
      (∀ x, (eFin x : F') = e x) ∧ (∀ x, (eInf x : F') = e x) ∧
      w.hom ≫ toBase R' F' j' = toBase R F j ≫ Spec.map (CommRingCat.ofHom e₀.symm.toRingHom) ∧
      Spec.map (CommRingCat.ofHom eFin.toRingHom) ≫ ιFin R F j = ιFin R' F' j' ≫ w.inv ∧
      Spec.map (CommRingCat.ofHom eInf.toRingHom) ≫ ιInf R F j = ιInf R' F' j' ≫ w.inv := by sorry
