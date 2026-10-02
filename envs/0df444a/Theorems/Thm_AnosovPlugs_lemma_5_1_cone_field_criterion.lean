-- Prove2me | Theorems.Thm_AnosovPlugs_lemma_5_1_cone_field_criterion
-- name    : AnosovPlugs.lemma_5_1_cone_field_criterion
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-02T10:12:31.036537+00:00
-- url     : https://prove2.me/theorems/4cea7c04-967d-4d3e-94ce-c78634a53526
-- title:
--   Lemma 5.1 (Béguin–Bonatti–Yu): invariant cone fields for the return map make the glued flow Anosov
-- statement:
--   Let $(U,Y)$ be a saddle hyperbolic plug with filling MS laminations, with invariant foliations $\mathcal G^s,\mathcal G^u$ in normal form (Proposition 4.2). Let $\psi:\partial^{out}U\to\partial^{in}U$ be a strongly transverse gluing map, and let $\Theta_\psi:=\psi\circ\Gamma$ be the return map of the glued flow on $\partial^{in}U$, where $\Gamma$ is the crossing map of the plug.
--
--   Assume that there are two continuous cone fields $C^s_{in}$ and $C^u_{in}$ on $\partial^{in}U$ such that
--
--   1. $C^u_{in}$ is invariant under $d\Theta_\psi$ and $C^s_{in}$ is invariant under $d\Theta_\psi^{-1}$, and vectors in $C^u_{in}$ (resp. $C^s_{in}$) are uniformly expanded by $d\Theta_\psi$ (resp. $d\Theta_\psi^{-1}$) for some Riemannian metric;
--   2. $C^u_{in}$ contains the directions tangent to $\mathcal G^u_{in}$ and to $\psi_*\mathcal G^u_{out}$, and contains neither the direction tangent to $\mathcal G^s_{in}$ nor the direction tangent to $\psi_*\mathcal G^s_{out}$;
--   3. $C^s_{in}$ contains the directions tangent to $\mathcal G^s_{in}$ and to $\psi_*\mathcal G^s_{out}$, and contains neither the direction tangent to $\mathcal G^u_{in}$ nor the direction tangent to $\psi_*\mathcal G^u_{out}$.
--
--   Then the vector field $Z_\psi$ induced by $Y$ on the closed manifold $U/\psi$ is Anosov:
--   $$ Z_\psi\ \text{is a hyperbolic vector field on all of}\ U/\psi. $$
--
--   This lemma reduces the hyperbolicity of the glued flow to a statement about its first return map on the entrance boundary; it is the criterion that Theorem 1.5 verifies.
--
--   **Formalization Note** As in the mission's main theorem, $U/\psi$ is not a quotient type: the conclusion holds for every closed smooth 3-manifold $N$ with a surjective $C^1$ immersion $q:U\to N$ realising the self-gluing by $\psi$ and pushing $Y$ to $Z$ (`IsSelfGluing`), and "Anosov" is `IsHyperbolicSet Z univ`. A cone field is given by a continuous family of symmetric $3\times 3$ matrices $Q$: the cone at $x$ is the set of tangent vectors $v$ to the boundary with $v^{\mathsf T}Q(x)v\ge 0$ (`IsConeField`, `cone`). Invariance and expansion of $C^s_{in}$ under $d\Theta_\psi^{-1}$ are stated without inverting: a vector whose image lies in $C^s_{in}$ lies in $C^s_{in}$ and is longer than its image by the factor $\mu>1$. The hypothesis block is the predicate `ConeFieldHypotheses`. It omits two of the paper's exclusions (the direction of $\psi_*\mathcal G^s_{out}$ from $C^u_{in}$ and the direction of $\mathcal G^u_{in}$ from $C^s_{in}$): the proof of Lemma 5.1 does not use them, and the gluing map produced in Section 5.1 need not satisfy them. The formal statement is therefore slightly stronger than the printed lemma, with the same proof.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Item numbers below follow arXiv v1; the published version shifts section numbers by one (arXiv §5 = GT §6). Lemma 5.1, p. 22 of arXiv v1 (Section 5.1, Reduction of Theorem 1.5 to a perturbation of the return map).

import Mathlib
import Definitions.Def_AnosovPlugs_Section5

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem lemma_5_1_cone_field_criterion {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (Y : (x : U) → TangentSpace I3 x) (φ₁ ψ : U → U)
    (As Au : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3)))
    (Qs Qu : U → Matrix (Fin 3) (Fin 3) ℝ)
    (hY : IsFillingHyperbolicPlug Y) (hYnoAR : NoAttractorNorRepeller Y)
    (hφ₁ : IsStronglyTransverseGluing Y φ₁) (hnf : IsNormalForm Y φ₁ As Au)
    (hψ : IsStronglyTransverseGluing Y ψ)
    (hQs : IsConeField Qs (inBoundary Y)) (hQu : IsConeField Qu (inBoundary Y))
    (hcone : ConeFieldHypotheses Y ψ As Au Qs Qu) :
    ∀ (N : Type) [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
      [IsManifold I3 ∞ N] [T2Space N] [CompactSpace N] [BoundarylessManifold I3 N]
      (Z : (y : N) → TangentSpace I3 y) (q : U → N),
      IsSelfGluing Y ψ Z q → IsHyperbolicSet Z univ := by sorry

end AnosovPlugs
