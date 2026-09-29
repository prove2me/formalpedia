-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos
-- name    : AlgebraicGeometry.Polarisation.closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/032fa8c4-4de4-5444-85ca-1e5128ceba27
-- title:
--   Very ampleness of mathcal L₀^{⊗ n} for n≥ 4
-- statement:
--   Let $k$ be an algebraically closed field, $f : A \to \operatorname{Spec} k$ a morphism of schemes, and $L$ a relative group law for $f$, i.e. a functorial group structure (multiplication, unit, inverse, associativity, the two unit laws, left inverse, and naturality under base change of the test scheme) on the sets of $t$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for all $t : T \to \operatorname{Spec} k$; assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre of $f$ is connected, and $f$ carries some relative group law. Let $\mathcal L_0$ be a module object on $A$ which is invertible (every point has a neighbourhood $U$ with the restriction of $\mathcal L_0$ to $U$ isomorphic to the unit sheaf), and suppose `KernelTrivial` holds for $\mathcal L_0$: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every $t$-point $x$ of $A$, if the pullback along the slice $\operatorname{sliceAt} x$ of the Mumford bundle $m^*\mathcal L_0 \otimes p_1^*\mathcal L_0^{\vee} \otimes p_2^*\mathcal L_0^{\vee}$ on $A\times_k A$ is, locally over the base $\operatorname{Spec} R$, isomorphic to the unit object, then $x$ is the unit $t$-point. Suppose further that, for the $k$-algebra structure on $\Gamma(A,\top)$ coming from $f$ and the induced $k$-module structure on $\Gamma(\mathcal L_0,\top)$, one has $\operatorname{finrank}_k \Gamma(\mathcal L_0,\top) > 0$. Then for every $n \ge 4$ and every module object $\mathcal N$ on $A$ isomorphic to the $n$-fold tensor power $\mathcal L_0^{\otimes n}$ (defined by $\mathcal L_0^{\otimes 0} = \mathbf 1$, $\mathcal L_0^{\otimes (m+1)} = \mathcal L_0^{\otimes m} \otimes \mathcal L_0$), the predicate `ClosedImmersionBySections` holds for $\mathcal N$ and $f$: there are an $N$ and a projective presentation of $\mathcal N$ over $f$ of size $N$ — global sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal N, \top)$ together with a morphism $\pi_{\mathcal N} : A \to \operatorname{Proj} k[X_0,\dots,X_N]$ over $\operatorname{Spec} k$ such that $\sigma_i$ frames $\mathcal N$ on every open contained in the preimage of the basic open set $D(X_i)$ and such that the pullbacks of the ratios $X_j/X_i$ carry $\sigma_i$ to $\sigma_j$ there — whose structure morphism to projective space is a closed immersion.
--
--   This is the Lefschetz very-ampleness theorem in the case of a principal invertible sheaf: on an abelian variety over an algebraically closed field, if the stabiliser group scheme $K(\mathcal L_0)$ is trivial and $\mathcal L_0$ has a nonzero global section, then $\mathcal L_0^{\otimes n}$ embeds $A$ in projective space for $n \ge 4$, with the two passages to the quotient $A/K(\mathcal L_0)$ of the general proof collapsing. It is used to produce projective embeddings of fake elliptic curves from canonical polarisations, via the corollaries for the third and fourth tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓛₀, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓛₀, ⊤))
    (n : ℕ) (hn : 4 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀.tensorPow n) :
    Scheme.Modules.ClosedImmersionBySections 𝓝 f := by sorry
