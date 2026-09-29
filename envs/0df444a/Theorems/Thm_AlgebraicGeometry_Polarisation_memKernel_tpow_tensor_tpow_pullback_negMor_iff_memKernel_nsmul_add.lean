-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add
-- name    : AlgebraicGeometry.Polarisation.memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/acf5b593-ce40-53cb-82f3-07ccfa35d161
-- title:
--   Kernel of mathcal L₀^{⊗ a}⊗([-1]^*mathcal L₀)^{⊗ b} and (a+b)y
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and $L$ a relative group law for $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ over arbitrary $t : T \to \operatorname{Spec} S$, assumed commutative; let $f$ satisfy the bundle of abelian-scheme properties (smooth, proper, geometrically connected fibres, and admitting a relative group law). Let $\mathcal L_0$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood on which $\mathcal L_0$ restricts to the unit module. Let $a, b$ be natural numbers with $a + b \ge 1$, let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$ a morphism, and $y$ a section of $f$ over $t$. Then $y$ lies in the kernel of the tensor power $\mathcal L_0^{\otimes a} \otimes ([-1]^*\mathcal L_0)^{\otimes b}$, where $[-1] =$ `negMor f L` is the inverse of the identity point, if and only if the $(a+b)$-fold sum $(a+b)\cdot y$ computed with $L$ lies in the kernel of $\mathcal L_0$. Here membership in the kernel of an invertible module $\mathcal L$ at a point $x$ means that the pullback along the slice $\operatorname{Spec} R \times_S A \to A \times_S A$, $(\mathrm{pr}_1, \mathrm{pr}_2 \circ x)$, of the Mumford bundle $m^*\mathcal L \otimes \mathrm{pr}_1^*\mathcal L^\vee \otimes \mathrm{pr}_2^*\mathcal L^\vee$ is isomorphic to the unit module after restriction over some open neighbourhood of each point of the base $\operatorname{Spec} R$.
--
--   This is the standard multiplicativity computation for Mumford's bundle $\Lambda(\mathcal L)$, computing the kernel $K(\mathcal L_0^{\otimes a} \otimes ([-1]^*\mathcal L_0)^{\otimes b})$ as the preimage of $K(\mathcal L_0)$ under multiplication by $a+b$; the case $b = 0$ recovers $K(\mathcal L_0^{\otimes a})$ and the case $(a,b)=(1,1)$ the symmetric bundle. It is used in the treatment of polarisations of the given type, in particular by `memKernel_iff_nsmul_eq_one_of_kernelTrivial_of_iso_tpow_tensor_tpow` and in the nonvanishing of $a+b$ in the ambient ring for symmetric polarisations over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (a b : ℕ) (hab : 1 ≤ a + b)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f) :
    MemKernel f L (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) b) t y ↔
      MemKernel f L 𝓛₀ t (L.nsmul t (a + b) y) := by sorry
