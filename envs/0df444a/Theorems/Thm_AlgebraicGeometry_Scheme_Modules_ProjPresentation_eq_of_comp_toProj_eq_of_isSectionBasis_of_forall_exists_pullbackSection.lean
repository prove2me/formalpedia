-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/18d18146-9065-5353-a7ff-622527b5237a
-- title:
--   Injectivity on dual-number points of a complete linear system
-- statement:
--   Let $k$ be a field, let $f : X \to \operatorname{Spec} k$ be a scheme over $k$, let $\mathcal N$ be a sheaf of $\mathcal O_X$-modules, and let $\mathfrak P$ be a `ProjPresentation` of $\mathcal N$ relative to $f$ of size $N$: global sections $\sigma_0,\dots,\sigma_N$ of $\mathcal N$ together with a morphism $\mathfrak P.\mathrm{toProj} : X \to \mathbb P^N_k$ over $\operatorname{Spec} k$ such that on any open contained in the preimage of the chart $\{x_i \neq 0\}$ multiplication by $\sigma_i$ is a bijection from functions to sections of $\mathcal N$, and such that the pullback of $x_j/x_i$ times $\sigma_i$ equals $\sigma_j$ on that preimage. Assume: (i) `IsSectionBasis`, i.e. $c \mapsto \sum_i f^{\sharp}(c_i)\,\sigma_i$ is a bijection $k^{N+1} \to \Gamma(\mathcal N, X)$; (ii) for any two distinct sections $a \neq b$ of $f$ over $\operatorname{Spec} k$ there is a global section $s : \mathbf 1 \to \mathcal N$ whose pullback along $a$ vanishes and whose pullback along $b$ does not; (iii) for every $P : \operatorname{Spec} k[\varepsilon] \to X$ over $\operatorname{Spec} k$ which differs from the constant lift of its underlying $k$-point $P \circ \operatorname{Spec}(\varepsilon \mapsto 0)$, there is a global section $s$ of $\mathcal N$ vanishing at that underlying $k$-point with nonzero pullback along $P$. Then any two $k[\varepsilon]$-points $P, Q$ of $X$ over $\operatorname{Spec} k$ with $P \circ \mathfrak P.\mathrm{toProj}$ (diagrammatically $P \;\!\mathfrak P.\mathrm{toProj}$, i.e. $\mathfrak P.\mathrm{toProj} \circ P$) equal to $\mathfrak P.\mathrm{toProj} \circ Q$ are equal.
--
--   This is the dual-number half of the classical criterion that a complete linear system separating points and tangent vectors defines an immersion: it upgrades separation of points and of tangent vectors to injectivity of the associated morphism to $\mathbb P^N_k$ on points with values in $k[\varepsilon]$, with no finiteness hypothesis on $X$ and no assumption that $k$ is algebraically closed. It is used in the construction of projective embeddings of polarised abelian schemes, where the linear system comes from a high tensor power of a line bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (𝓝 : X.Modules)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓝 𝔓.σ)
    (hpt : ∀ a b : Spec (CommRingCat.of k) ⟶ X, a ≫ f = 𝟙 _ → b ≫ f = 𝟙 _ → a ≠ b →
      ∃ s : 𝟙_ X.Modules ⟶ 𝓝, Scheme.Modules.pullbackSection a s = 0 ∧ Scheme.Modules.pullbackSection b s ≠ 0)
    (htan : ∀ P : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      P ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
        (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P) →
      ∃ s : 𝟙_ X.Modules ⟶ 𝓝,
        Scheme.Modules.pullbackSection (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P) s = 0 ∧
          Scheme.Modules.pullbackSection P s ≠ 0)
    (P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X)
    (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hQ : Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (h : P ≫ 𝔓.toProj = Q ≫ 𝔓.toProj) :
    P = Q := by sorry
