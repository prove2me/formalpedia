-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_pullbackSection_eq_zero_and_ne_zero_of_ne_of_iso_tensorPow_of_kernelTrivial
-- name    : AlgebraicGeometry.Polarisation.exists_pullbackSection_eq_zero_and_ne_zero_of_ne_of_iso_tensorPow_of_kernelTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/6bb69ea9-5772-556a-b531-b026dc8e8b6d
-- title:
--   Sections of mathcal L₀^{⊗ n} separate k-points for n≥ 4
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over arbitrary $k$-schemes $t : T \to \operatorname{Spec} k$, compatible with base change along $T' \to T$; assume $L$ is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that every fibre $f^{-1}(s)$ is connected, and that $f$ admits a relative group law. Let $\mathcal L_0$ be a module object on $A$ which is invertible, in the sense that every point of $A$ has a neighbourhood $U$ on which the restriction of $\mathcal L_0$ is isomorphic to the unit module. Assume `KernelTrivial`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every point $x$ of $A$ over $t$, if the slice at $x$ of the Mumford bundle $(\mathrm{add}^*\mathcal L_0) \otimes \mathrm{pr}_1^*\mathcal L_0^{\vee} \otimes \mathrm{pr}_2^*\mathcal L_0^{\vee}$ on $A \times_{\operatorname{Spec} k} A$ becomes isomorphic to the unit locally on $\operatorname{Spec} R$, then $x$ is the identity point $L.\mathrm{one}\, t$. Assume further that $\Gamma(\mathcal L_0, \top)$ has positive finite rank as a $k$-module, $k$ acting through $\Gamma(A,\top)$ via $f$. Finally let $n \ge 4$, let $\mathcal N$ be a module object on $A$ with an isomorphism $\mathcal N \cong \mathcal L_0^{\otimes n}$ (the tensor power formed by iterating $\,\cdot \otimes \mathcal L_0$ from the unit), and let $a \ne b$ be two sections of $f$ over $\operatorname{Spec} k$. Then there is a global section $s : \mathbb 1 \to \mathcal N$ whose pullback along $a$ vanishes and whose pullback along $b$ does not.
--
--   This is the separation-of-points half of the statement that for an invertible sheaf with positive $h^0$ and trivial theta group kernel $K(\mathcal L_0) = \{e\}$ on an abelian variety, $\mathcal L_0^{\otimes n}$ with $n \ge 4$ has enough sections to separate $k$-points (Mumford, Abelian Varieties, §17). It feeds the verification that the associated map to projective space is injective on points, used in [`AlgebraicGeometry.Polarisation.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le`](thm.html#AlgebraicGeometry.Polarisation.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_pullbackSection_eq_zero_and_ne_zero_of_ne_of_iso_tensorPow_of_kernelTrivial.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_pullbackSection_eq_zero_and_ne_zero_of_ne_of_iso_tensorPow_of_kernelTrivial
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓛₀, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓛₀, ⊤))
    (n : ℕ) (hn : 4 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀.tensorPow n)
    (a b : Spec (CommRingCat.of k) ⟶ A) (ha : a ≫ f = 𝟙 _) (hb : b ≫ f = 𝟙 _) (hab : a ≠ b) :
    ∃ s : 𝟙_ A.Modules ⟶ 𝓝, Scheme.Modules.pullbackSection a s = 0 ∧ Scheme.Modules.pullbackSection b s ≠ 0 := by sorry
