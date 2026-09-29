-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_oneProdNsmul_mumfordBundle_iso_mumfordBundle_tensorPow
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_oneProdNsmul_mumfordBundle_iso_mumfordBundle_tensorPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c9dcf2b3-dd3f-5456-9e4f-15f0adac46d4
-- title:
--   Pullback of the Mumford bundle along 1 × [ℓ]
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law on $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ over each $k$-scheme $t : T \to \operatorname{Spec} k$, natural in $T$. Assume $L$ is commutative, and that $f$ satisfies the property bundle `AbelianSchemePropertyBundle` ($f$ smooth, proper, with connected fibres, and admitting some relative group law). Let $g$ be a natural number such that every fibre $f^{-1}(s)$, $s$ a point of $\operatorname{Spec} k$, has topological Krull dimension $g$. Let $\mathcal{M}$ be an object of `A.Modules` that is invertible, meaning every point of $A$ has an open neighbourhood $U$ over which the pullback of $\mathcal{M}$ along $U \hookrightarrow A$ is isomorphic to the unit module, and let $\ell$ be a natural number. Write $\Lambda(\mathcal{L}) = m^*\mathcal{L} \otimes (p_1^*\mathcal{L}^\vee \otimes p_2^*\mathcal{L}^\vee)$ for the Mumford bundle on $A \times_{\operatorname{Spec} k} A$, where $m$ is the addition morphism obtained by multiplying the two projections in $L$, and $\mathcal{L}^\vee$ is the internal hom into the unit; write $\mathcal{M}^{\otimes \ell}$ for the $\ell$-fold tensor power defined by $\mathcal{M}^{\otimes 0} = \mathbf{1}$, $\mathcal{M}^{\otimes (n+1)} = \mathcal{M}^{\otimes n} \otimes \mathcal{M}$, and $[\ell] : A \to A$ for the $\ell$-fold sum of the identity section in $L$. The assertion is that there exists an isomorphism of modules on $A \times_{\operatorname{Spec} k} A$ between the pullback of $\Lambda(\mathcal{M})$ along the morphism $(p_1, [\ell] \circ p_2)$ and $\Lambda(\mathcal{M}^{\otimes \ell})$; only the existence of such an isomorphism is asserted, no particular one being chosen.
--
--   This is the standard compatibility of the Mumford (theta) bundle with multiplication by $\ell$ in the second variable, $(1 \times [\ell])^*\Lambda(\mathcal{M}) \cong \Lambda(\mathcal{M}^{\otimes \ell})$, in the relative-group-law formulation used here for abelian schemes over an algebraically closed field. It feeds the case $\ell = 2$ of the same identity and the construction of the Riemann-form style isomorphism $\Lambda(\mathcal{M}) \cong \Lambda(\mathcal{M})^{\otimes \ell} \otimes \cdots$ used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_oneProdNsmul_mumfordBundle_iso_mumfordBundle_tensorPow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_oneProdNsmul_mumfordBundle_iso_mumfordBundle_tensorPow
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (ℓ : ℕ) :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj (mumfordBundle f L 𝓜) ≅
      mumfordBundle f L (𝓜.tensorPow ℓ)) := by sorry
