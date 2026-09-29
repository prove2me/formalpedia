-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/cde31945-882c-58cb-ba29-90e0e1d383ec
-- title:
--   Pullback of a curve twist along a constant section
-- statement:
--   Let $k$ be a field, let $C$ be a scheme and $c \colon C \to \operatorname{Spec} k$ a morphism, and let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c`, i.e. a morphism $\varepsilon \colon \operatorname{Spec} k \to C$ with $\varepsilon$ followed by $c$ equal to the identity. Let $N$ be a rigidified line bundle for $c$, $\varepsilon$ over the identity of $\operatorname{Spec} k$: thus $N.L$ is a sheaf of modules on the fibre product $C \times_{\operatorname{Spec} k} \operatorname{Spec} k$ which is invertible, in the sense that every point has an open neighbourhood $U$ over which the restriction of $N.L$ is isomorphic to the unit sheaf of $U$, together with an isomorphism of the pullback of $N.L$ along the section `rigSection c (𝟙 _) ε` (the morphism into the fibre product with components $\varepsilon$ and the identity) with the unit sheaf. Let $P$ be a further section of $c$ in the same sense, and let $t \colon T \to \operatorname{Spec} k$ be any morphism of schemes. The assertion is that there exists an isomorphism between the pullback along `rigSection c t P` (the constant section $T \to C \times_{\operatorname{Spec} k} T$ with value $P$) of the module `(N.pullbackAlong ⟨t, _⟩).L`, that is, the pullback of $N.L$ along the base-change morphism $C \times_{\operatorname{Spec} k} T \to C \times_{\operatorname{Spec} k} \operatorname{Spec} k$ induced by $t$, and the monoidal unit of `T.Modules`.
--
--   The statement records that a line bundle pulled back from the curve to $C \times_k T$ becomes trivial when restricted along a constant section, because the restriction factors through a line bundle on $\operatorname{Spec} k$. It is used in the computation of theta bundles of translates, where it shows that the correction term attached to a point does not contribute twists coming from the curve; it is cited by [`AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso`](thm.html#AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso) and by [`AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso`](thm.html#AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
    {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t P)).obj (N.pullbackAlong ⟨t, Category.comp_id t⟩).L ≅
      𝟙_ T.Modules) := by sorry
