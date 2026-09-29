-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_schemeNsmul_pullback_translation_iso
-- name    : AlgebraicGeometry.RiemannForm.nonempty_pullback_schemeNsmul_pullback_translation_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/64a3e9f6-40f7-547a-9f8b-701e11ff8567
-- title:
--   Pullback along [n] of T_Q^*L for n-torsion Q
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative, and that $f$ satisfies the bundle of properties `AbelianSchemePropertyBundle`, namely $f$ smooth, $f$ proper, every fibre $f^{-1}(s)$ connected, and the existence of a relative group law. Let $\mathcal L$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of $U$. Let $n$ be a natural number and let $Q$ be an element of the additive group of $k$-points of $L$ with $n \cdot Q = 0$. Write $T_Q : A \to A$ for the translation morphism, the first component of $L$-multiplication of the identity point of $A$ by the constant point $Q$, and $[n] : A \to A$ for the $n$-fold $L$-sum of the identity point with itself. The conclusion asserts that there exists an isomorphism $[n]^*T_Q^*\mathcal L \cong [n]^*\mathcal L$ of modules on $A$.
--
--   This is the $\otimes$-free form of the statement that, for an $n$-torsion point $Q$ of an abelian variety, the line bundle $T_Q^*\mathcal L \otimes \mathcal L^{-1}$ lies in $\operatorname{Pic}^0$ and becomes trivial after pullback along multiplication by $n$. It supplies the existence half of the Riemann (Weil) pairing on $n$-torsion, and is used in the construction of level-pairing values and in the theta-group computation of commutators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_schemeNsmul_pullback_translation_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.nonempty_pullback_schemeNsmul_pullback_translation_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (n : ℕ) (Q : L.AlgPoints hc k) (hQ : n • Q = 0) :
    Nonempty ((Scheme.Modules.pullback (L.schemeNsmul n)).obj
        ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛) ≅
      (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) := by sorry
