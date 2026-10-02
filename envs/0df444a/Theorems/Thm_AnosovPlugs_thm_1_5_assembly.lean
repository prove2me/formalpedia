-- Prove2me | Theorems.Thm_AnosovPlugs_thm_1_5_assembly
-- name    : AnosovPlugs.thm_1_5_assembly
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-02T10:12:41.806749+00:00
-- url     : https://prove2.me/theorems/860bbaba-9bfc-4099-8004-3395c0c128cd
-- title:
--   Theorem 1.5 assembly (Béguin–Bonatti–Yu, §5.1): the perturbed gluing map is strongly transverse, strongly isotopic, and carries invariant cone fields
-- statement:
--   Let $(U,Y)$ be a saddle hyperbolic plug with filling MS laminations, $\varphi_1$ a strongly transverse gluing map, and $\mathcal G^s,\mathcal G^u$ invariant foliations in normal form (Proposition 4.2). Assume the conclusion of Proposition 5.2: for every $\lambda>1$ and $\varepsilon>0$ there are boundary diffeomorphisms $\psi^{in}_{\lambda,\varepsilon}$, $\psi^{out}_{\lambda,\varepsilon}$ with the four properties listed there.
--
--   Then there is a gluing map $\psi:\partial^{out}U\to\partial^{in}U$, namely $\psi=\psi^{in}_{\lambda,\varepsilon}\circ\varphi_1\circ\psi^{out}_{\lambda,\varepsilon}$ for $\varepsilon$ small enough and $\lambda$ large enough, such that
--
--   1. $\psi$ is a strongly transverse gluing map for $(U,Y)$;
--   2. $(U,Y,\psi)$ is strongly isotopic to $(U,Y,\varphi_1)$;
--   3. there exist continuous cone fields $C^s_{in}$, $C^u_{in}$ on $\partial^{in}U$ satisfying the hypotheses of Lemma 5.1 for the return map $\Theta_\psi=\psi\circ\Gamma$.
--
--   $$ \psi:=\psi^{in}\circ\varphi_1\circ\psi^{out}\quad\text{satisfies the cone-field criterion of Lemma 5.1.} $$
--
--   This is the argument of Section 5.1 that assembles Proposition 5.2 into Theorem 1.5: $\psi^{in}$ and $\psi^{out}$ are the identity near the laminations, so $\psi$ stays strongly transverse and isotopic to $\varphi_1$ (Claim 5.3 and the paragraph before it); the perturbed foliations stay uniformly transverse for small $\varepsilon$ (Claim 5.4); the return map expands the $\mathcal G^u_{in}$ directions by a factor $C\lambda$ (Claim 5.5); and for $\lambda$ large a cone field around $\mathcal G^u_{in}$ and $\varphi_{1*}\mathcal G^u_{out}$ is strictly invariant and expanded (Fact 5.6), with the symmetric construction for $C^s_{in}$.
--
--   **Formalization Note** The statement takes the family of Proposition 5.2 as a hypothesis (`∀ λ > 1, ∀ ε > 0, ∃ ψin ψout, Prop52Data …`) and concludes the existence of $\psi$ and of cone fields $Q^s,Q^u$ with `IsConeField` and `ConeFieldHypotheses`. The composite form of $\psi$ is not part of the formal conclusion.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Item numbers below follow arXiv v1; the published version shifts section numbers by one (arXiv §5 = GT §6). Section 5.1, 'Proof of Theorem 1.5 assuming Proposition 5.2', Claims 5.3, 5.4, 5.5 and Fact 5.6, pp. 23–25 of arXiv v1.

import Mathlib
import Definitions.Def_AnosovPlugs_Section5

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem thm_1_5_assembly {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (Y : (x : U) → TangentSpace I3 x) (φ₁ : U → U)
    (As Au : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3)))
    (hY : IsFillingHyperbolicPlug Y) (hYnoAR : NoAttractorNorRepeller Y)
    (hφ₁ : IsStronglyTransverseGluing Y φ₁) (hnf : IsNormalForm Y φ₁ As Au)
    (hfam : ∀ g : RiemannianMetric3 U, ∀ lam : ℝ, 1 < lam → ∀ eps : ℝ, 0 < eps →
      ∃ ψin ψout : U → U, Prop52Data Y g As Au lam eps ψin ψout) :
    ∃ ψ : U → U, IsStronglyTransverseGluing Y ψ ∧ StronglyIsotopic Y φ₁ Y ψ ∧
      ∃ Qs Qu : U → Matrix (Fin 3) (Fin 3) ℝ,
        IsConeField Qs (inBoundary Y) ∧ IsConeField Qu (inBoundary Y) ∧
        ConeFieldHypotheses Y ψ As Au Qs Qu := by sorry

end AnosovPlugs
