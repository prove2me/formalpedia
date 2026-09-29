-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso
-- name    : AlgebraicGeometry.RelPicard.nonempty_ajFamily_fibre_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b71a1a2a-7a02-5596-abeb-bceaaeed80d5
-- title:
--   Fibres of the Abel–Jacobi family over a k-point
-- statement:
--   Let $k$ be a field and let $a \colon A \to \operatorname{Spec} k$ be a separated morphism of schemes that is smooth of relative dimension $1$, and let $\varepsilon, t$ be sections of $a$, that is, morphisms $\operatorname{Spec} k \to A$ composing with $a$ to the identity of $\operatorname{Spec} k$. On $A \times_k A$ (the Lean pullback of $a$ along $a$) one has the module `ajFamily` $\varepsilon$, defined as the tensor product of the inverse module of the ideal of the degree-one relative effective Cartier divisor `diagDiv` attached to the section $\mathrm{id}_A$ of $a$ over the second factor (the diagonal, so $\mathcal O(\Delta)$) with the ideal module of the divisor `constDiv` $\varepsilon$ attached to the section $a$ followed by $\varepsilon$ (the constant section, so $\mathcal O(-(A \times \varepsilon))$); here each of these divisors consists of an ideal sheaf datum whose closed subscheme is finite, flat and locally of finite presentation over the base factor with all fibres of rank $1$, the ideal being the kernel of the graph of the relevant section. The assertion is that the pullback of `ajFamily` $\varepsilon$ along `baseChangeSnd` $a$ $t$, the morphism $A \times_k \operatorname{Spec} k \to A \times_k A$ induced by $\mathrm{id}_A$ on the first factor and by $t$ on the second, admits an isomorphism of modules on $A \times_k \operatorname{Spec} k$ to `pointSubBasepointModule` $t$ $\varepsilon$, the tensor product of the inverse module of the ideal of the point divisor of $t$ with the ideal module of the point divisor of $\varepsilon$ — in classical notation $(1 \times t)^{*}\bigl(\mathcal O(\Delta) \otimes \mathcal O(-(A \times \varepsilon))\bigr) \cong \mathcal O(t) \otimes \mathcal O(-\varepsilon)$. The conclusion is stated as the non-emptiness of the type of such isomorphisms, so no canonical choice is recorded.
--
--   This is the fibre computation for the Abel–Jacobi family on a smooth separated relative curve: the family $\mathcal O(\Delta) \otimes \mathcal O(-(A \times \varepsilon))$ on $A \times_k A$, viewed over the second factor, restricts over a $k$-point $t$ to the degree-zero line bundle $\mathcal O(t - \varepsilon)$. It is used in the identification of the class of $t - \varepsilon$ in the relative Picard group, cited by [`AlgebraicGeometry.RelPicard.isAlgEquivZero_pointSubBasepoint`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_pointSubBasepoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.nonempty_ajFamily_fibre_iso
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t)).obj (ajFamily (a := a) ε) ≅
      pointSubBasepointModule (a := a) t ε) := by sorry
