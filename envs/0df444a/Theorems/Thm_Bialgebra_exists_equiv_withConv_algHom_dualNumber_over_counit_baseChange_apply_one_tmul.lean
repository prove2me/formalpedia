-- Prove2me | Theorems.Thm_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul
-- name    : Bialgebra.exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/63e36bb3-674e-58cd-8f97-b5a3cc7ab1ee
-- title:
--   Base change of k[ε]-points over the counit
-- statement:
--   Let $R$ be a commutative ring, $k$ a commutative ring carrying an $R$-algebra structure, and $H$ a commutative ring carrying an $R$-bialgebra structure, with counit the $R$-algebra map $\varepsilon_H =$ `Bialgebra.counitAlgHom R H`. Consider, on one side, the type `WithConv (H →ₐ[R] DualNumber k)` of $R$-algebra maps $H \to k[\epsilon]$ into the dual numbers, taken with its convolution multiplication (the underlying map of an element $D$ being recovered as `D.ofConv`), restricted to those $D$ with $\mathrm{fst}(D.\mathrm{ofConv}\,h) = \varepsilon_H(h)$ in $k$, via the structure map $R \to k$, for every $h \in H$; and, on the other side, the $k$-algebra maps $D \colon k \otimes_R H \to k[\epsilon]$ with $\mathrm{fst}(D\,b)$ equal to the counit of the $k$-bialgebra $k \otimes_R H$ applied to $b$, for every $b$. The theorem asserts the existence of a bijection $\beta$ between these two subtypes such that for every $D$ in the first subtype and every $h \in H$ one has $(\beta D)(1 \otimes_R h) = D.\mathrm{ofConv}\,h$; that is, $\beta$ is given by extension of scalars along $h \mapsto 1 \otimes h$. No finiteness or flatness hypothesis occurs.
--
--   This is the tensor–Hom adjunction for commutative algebras in the form needed for functor-of-points computations: the $k[\epsilon]$-valued points of $\operatorname{Spec} H$ lying over the unit section agree with those of its base change $\operatorname{Spec}(k \otimes_R H)$ to $k$. It is used in the identification of the cotangent/tangent space at the origin of a group scheme after base change, being cited in the computation of the cotangent space of a model of a modular curve at $j = 0$ torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul
    (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
    (H : Type) [CommRing H] [Bialgebra R H] :
    ∃ β : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)} ≃
          {D : k ⊗[R] H →ₐ[k] DualNumber k //
            ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b},
      ∀ (D : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)})
        (h : H), (β D).1 ((1 : k) ⊗ₜ[R] h) = D.1.ofConv h := by sorry
