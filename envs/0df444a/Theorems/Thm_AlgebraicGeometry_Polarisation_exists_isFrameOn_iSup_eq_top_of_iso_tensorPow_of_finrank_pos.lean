-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isFrameOn_iSup_eq_top_of_iso_tensorPow_of_finrank_pos
-- name    : AlgebraicGeometry.Polarisation.exists_isFrameOn_iSup_eq_top_of_iso_tensorPow_of_finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/775d64e3-53b0-587b-8eab-3d1382391002
-- title:
--   Base-point freeness of M^{⊗ n}, n≥ 2
-- statement:
--   Let $k$ be an algebraically closed field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes (in the zeroth universe) equipped with a relative group law $L$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$; assume $L$ is commutative, and that $f$ satisfies the bundle of properties `AbelianSchemePropertyBundle`, namely $f$ is smooth, proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $\mathcal M$ be a module over $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ such that the pullback of $\mathcal M$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of rings-modules on $U$. Regard $\Gamma(A,\top)$ as a $k$-algebra via the map induced by $f$ on global sections, and $\Gamma(\mathcal M,\top)$ as a $k$-module through it; assume $0 < \operatorname{finrank}_k \Gamma(\mathcal M,\top)$. Let $n \ge 2$ and let $\mathcal N$ be a module over $A$ isomorphic to `𝓜.tensorPow n`, the $n$-fold tensor power built from the unit by repeated tensoring on the right by $\mathcal M$. Then there are $N \in \mathbb N$, global sections $\sigma_0,\dots,\sigma_N$ of $\mathcal N$ and opens $U_0,\dots,U_N$ of $A$ whose supremum is $\top$ such that each $\sigma_i$ is a frame on $U_i$: for every open $W \le U_i$, multiplication $g \mapsto g \cdot \sigma_i|_W$ is a bijection $\Gamma(A,W) \to \Gamma(\mathcal N,W)$.
--
--   This is the statement that on an abelian variety over an algebraically closed field an effective invertible sheaf has base-point free $n$-th tensor power for $n \ge 2$ — here in the explicit form of finitely many global sections each framing $\mathcal N$ on a member of an open cover. It feeds the construction of projective embeddings and stabiliser computations in the polarisation development, being cited by [`AlgebraicGeometry.Polarisation.closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos`](thm.html#AlgebraicGeometry.Polarisation.closedImmersionBySections_of_iso_tensorPow_of_kernelTrivial_of_finrank_pos) and by the two `isInStabilizer_tensorPow_mul_inv_…` results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_isFrameOn_iSup_eq_top_of_iso_tensorPow_of_finrank_pos.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_isFrameOn_iSup_eq_top_of_iso_tensorPow_of_finrank_pos
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓜, ⊤))
    (n : ℕ) (hn : 2 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow n) :
    ∃ (N : ℕ) (σ : Fin (N + 1) → Γ(𝓝, ⊤)) (U : Fin (N + 1) → A.Opens),
      iSup U = ⊤ ∧ ∀ i, Scheme.Modules.IsFrameOn (σ i) (U i) := by sorry
