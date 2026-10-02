-- Prove2me | Theorems.Thm_AnosovPlugs_prop_5_2_return_map_perturbation
-- name    : AnosovPlugs.prop_5_2_return_map_perturbation
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-02T10:12:31.991005+00:00
-- url     : https://prove2.me/theorems/12ed398e-ce88-436b-ace1-89ae5f32858a
-- title:
--   Proposition 5.2 (Béguin–Bonatti–Yu): perturbing the entrance and exit boundaries to make the crossing map strongly hyperbolic
-- statement:
--   Let $(U,Y)$ be a saddle hyperbolic plug with filling MS laminations, $\varphi_1:\partial^{out}U\to\partial^{in}U$ a strongly transverse gluing map, and $\mathcal G^s,\mathcal G^u$ invariant foliations in normal form (Proposition 4.2). Let $\Gamma:\partial^{in}U\setminus L^s\to\partial^{out}U\setminus L^u$ be the crossing map of the plug (the first exit point of the forward orbit, Definition 2.13).
--
--   Then for every $\lambda>1$ and every $\varepsilon>0$ there exist diffeomorphisms $\psi^{in}:\partial^{in}U\to\partial^{in}U$ and $\psi^{out}:\partial^{out}U\to\partial^{out}U$ such that
--
--   1. $\psi^{in}$ is the identity on a neighbourhood of the entrance lamination $L^s$ and $\psi^{out}$ is the identity on a neighbourhood of the exit lamination $L^u$;
--   2. $\psi^{in}$ preserves each leaf of $\mathcal G^u_{in}$ and $\psi^{out}$ preserves each leaf of $\mathcal G^s_{out}$;
--   3. the foliation $(\psi^{in})^{-1}_*\mathcal G^s_{in}$ is $\varepsilon$-$C^1$-close to $\mathcal G^s_{in}$, and $(\psi^{out})_*\mathcal G^u_{out}$ is $\varepsilon$-$C^1$-close to $\mathcal G^u_{out}$;
--   4. the derivative of $\Gamma\circ\psi^{in}$ expands every vector $u$ tangent to $\mathcal G^u_{in}$ by a factor larger than $\lambda$,
--   $$\|(\Gamma\circ\psi^{in})_*u\|>\lambda\|u\|,$$
--   and the derivative of $(\psi^{out}\circ\Gamma)^{-1}$ expands every vector tangent to $\mathcal G^s_{out}$ by a factor larger than $\lambda$.
--
--   These perturbations are the heart of the proof of Theorem 1.5: composing them with $\varphi_1$ produces the gluing map whose return map admits invariant expanding cone fields.
--
--   **Formalization Note** Closeness of two foliations is stated as closeness of their tangent lines at every point: unit tangent vectors at chart distance less than $\varepsilon$ (`LinesClose`). Norms and derivatives are taken in the half-space charts of $U$, in which tangent spaces are $\mathbb R^3$; derivatives along the boundary surface are `mfderivWithin`, which is determined on tangent vectors to the boundary. The four items form the predicate `Prop52Data`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Item numbers below follow arXiv v1; the published version shifts section numbers by one (arXiv §5 = GT §6). Proposition 5.2, p. 23 of arXiv v1 (Section 5.1; proof in Section 5.2).

import Mathlib
import Definitions.Def_AnosovPlugs_Section5

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem prop_5_2_return_map_perturbation {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (Y : (x : U) → TangentSpace I3 x) (φ₁ : U → U)
    (As Au : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3)))
    (hY : IsFillingHyperbolicPlug Y) (hYnoAR : NoAttractorNorRepeller Y)
    (hφ₁ : IsStronglyTransverseGluing Y φ₁) (hnf : IsNormalForm Y φ₁ As Au) :
    ∀ g : RiemannianMetric3 U, ∀ lam : ℝ, 1 < lam → ∀ eps : ℝ, 0 < eps →
      ∃ ψin ψout : U → U, Prop52Data Y g As Au lam eps ψin ψout := by sorry

end AnosovPlugs
