-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp_dualNumber
-- name    : AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/ceaa1b7d-ae0f-5e1a-9f02-b69034d88975
-- title:
--   Tangent vector killing all vanishing sections stabilises mathcal L₀^{⊗ j}
-- statement:
--   Let $k$ be an algebraically closed field, $f : A \to \operatorname{Spec} k$ a morphism of schemes, $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$), assumed commutative, and let $f$ satisfy the bundle of properties `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre of the underlying map is connected, and $f$ admits a relative group law. Let $\mathcal L_0$ be a module on $A$ which is invertible (locally isomorphic to the structure sheaf), with $\dim_k \Gamma(\mathcal L_0,\top) > 0$ for the $k$-structure induced by $f$. Let $j, n$ be naturals with $2 \le j$ and $j+1 \le n$, and $\mathcal N$ a module on $A$ with an isomorphism $\mathcal N \cong \mathcal L_0^{\otimes n}$, where the tensor power is formed recursively. Write $\iota_\varepsilon : \operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$ for the map induced by $k \to k[\varepsilon] = \mathrm{TrivSqZeroExt}\,k\,k$ and $o : \operatorname{Spec} k \to \operatorname{Spec} k[\varepsilon]$ for the map induced by the first-coordinate algebra map $k[\varepsilon] \to k$. Let $P$ and $a_\varepsilon$ be $k[\varepsilon]$-points of $A$ over $\iota_\varepsilon$, with $a_\varepsilon = \iota_\varepsilon$ followed by $o$ followed by $P$, i.e. $a_\varepsilon$ is the constant $k[\varepsilon]$-point at the $k$-point $a = o$ followed by $P$. Assume that every global section $s : \mathbf 1 \to \mathcal N$ whose pullback along $a$ vanishes has vanishing pullback along $P$. Then, with the group structure on $k[\varepsilon]$-points coming from $L$, the point $P \cdot a_\varepsilon^{-1}$ lies in the stabiliser of $\mathcal L_0^{\otimes j}$: the pullback of $\mathcal L_0^{\otimes j}$ along translation by $P \cdot a_\varepsilon^{-1}$ on $A \times_{\operatorname{Spec} k} \operatorname{Spec} k[\varepsilon]$ and its pullback along the first projection become isomorphic over the preimages of the members of an open cover of $\operatorname{Spec} k[\varepsilon]$.
--
--   This is the infinitesimal (dual-number) form of the statement that a point at which all sections of $\mathcal L_0^{\otimes n}$ vanishing at the base point again vanish gives, after translation to the origin, an element of the stabiliser $K(\mathcal L_0^{\otimes j})$; classically it is the tangent-vector half of Mumford's analysis of the maps attached to powers of an invertible sheaf on an abelian variety. It feeds the construction of a section of $\mathcal L_0^{\otimes n}$ vanishing at a prescribed point but not along a prescribed tangent direction, when the stabiliser of $\mathcal L_0^{\otimes j}$ is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp_dualNumber.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp_dualNumber
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓛₀, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓛₀, ⊤))
    (j n : ℕ) (hj : 2 ≤ j) (hjn : j + 1 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀.tensorPow n)
    (P aε : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) f)
    (haε : aε.1 = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P.1))
    (H : ∀ s : 𝟙_ A.Modules ⟶ 𝓝,
      Scheme.Modules.pullbackSection (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P.1) s = 0 →
        Scheme.Modules.pullbackSection P.1 s = 0) :
    L.IsInStabilizer (𝓛₀.tensorPow j) (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
      (letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))); P * aε⁻¹) := by sorry
