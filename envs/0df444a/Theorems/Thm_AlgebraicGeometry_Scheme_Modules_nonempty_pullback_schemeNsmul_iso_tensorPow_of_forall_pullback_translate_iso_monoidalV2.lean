-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/8abdb346-0217-58da-a028-6224c6084334
-- title:
--   [n]^*N ≅ N^{⊗ n} for translation-invariant invertible N
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme over $\operatorname{Spec} k$ via $f : A \to \operatorname{Spec}(k)$, and let $L$ be a `RelativeGroupLaw` for $f$: a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of lifts of a morphism $t : T \to \operatorname{Spec}(k)$ through $f$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverse, and naturality under base change $\psi : T' \to T$ with $\psi \circ t = t'$. Assume $L$ is commutative, i.e. its multiplication on every such set of lifts is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that each fibre $f^{-1}(s)$ is connected, and that $f$ admits a relative group law. Let $N$ be an object of $A$-modules which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $(\text{pullback of }N\text{ along }U \hookrightarrow A)$ isomorphic to the unit module on $U$, and assume that for every lift $x$ of the identity of $\operatorname{Spec}(k)$ through $f$ the pullback of $N$ along the translation $L.\mathrm{translate}\,x$ is isomorphic to $N$. Then for every natural number $n$ there exists an isomorphism between the pullback of $N$ along $L.\mathrm{schemeNsmul}\,n$ — the underlying morphism $A \to A$ of the $n$-fold product of the identity point with itself — and $N.\mathrm{tensorPow}\,n$, defined by $N^{\otimes 0} = \mathbf 1$ and $N^{\otimes(m+1)} = N^{\otimes m} \otimes N$.
--
--   This is the standard fact that multiplication by $n$ acts on $\mathrm{Pic}^0$ of an abelian variety by $N \mapsto N^{\otimes n}$, here with membership in $\mathrm{Pic}^0$ expressed as invertibility together with invariance under all translations by points. It is used in the construction of Riemann forms attached to such line bundles, via [`AlgebraicGeometry.RiemannForm.nonempty_pullback_schemeNsmul_pullback_translation_iso`](thm.html#AlgebraicGeometry.RiemannForm.nonempty_pullback_schemeNsmul_pullback_translation_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hN0 : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      Nonempty ((Scheme.Modules.pullback (L.translate x)).obj N ≅ N))
    (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (L.schemeNsmul n)).obj N ≅ N.tensorPow n) := by sorry
