-- Prove2me | Theorems.Thm_AnosovPlugs_stronglyIsotopic_trans
-- name    : AnosovPlugs.stronglyIsotopic_trans
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T09:06:32.837486+00:00
-- url     : https://prove2.me/theorems/bd240e68-c32c-423d-8971-7106bbc7e4de
-- title:
--   Strong isotopy of gluing data is transitive (Béguin–Bonatti–Yu, Definition 2.27)
-- statement:
--   Let $U$ be a compact 3-manifold with boundary and let $(U,X_0,\varphi_0)$, $(U,X_1,\varphi_1)$, $(U,X_2,\varphi_2)$ be hyperbolic plugs with filling MS laminations, each endowed with a strongly transverse gluing map. If $(U,X_0,\varphi_0)$ is strongly isotopic to $(U,X_1,\varphi_1)$ and $(U,X_1,\varphi_1)$ is strongly isotopic to $(U,X_2,\varphi_2)$, then
--   $$ (U,X_0,\varphi_0)\ \text{is strongly isotopic to}\ (U,X_2,\varphi_2). $$
--
--   Recall (Definition 2.27) that two such triples are strongly isotopic when they are joined by a continuous path $(U,X_t,\varphi_t)_{t\in[0,1]}$ of hyperbolic plugs with filling MS laminations and strongly transverse gluing maps. The proof concatenates the two paths and reparametrises time.
--
--   Theorem 1.5 produces its gluing map in two steps (Proposition 4.2, then the perturbation of Section 5.1); this lemma combines the two strong isotopies into the single one that the theorem asserts.
--
--   **Formalization Note** `StronglyIsotopic X₀ φ₀ X₁ φ₁` (Definition 3.28 in the mission's definitions) asks for a path $t\mapsto(X_t,\varphi_t)$ with $X_0,X_1$ prescribed, $\varphi_0,\varphi_1$ prescribed on the respective exit boundaries, each $(U,X_t,\varphi_t)$ a filling hyperbolic plug with a strongly transverse gluing map, continuity of the tangent maps of $x\mapsto X_t(x)$ jointly in $(t,v)$, and joint continuity of $(t,x)\mapsto\varphi_t(x)$ on $\{x\in\partial^{out}_{X_t}U\}$. The statement is the transitivity of this relation for a fixed $U$.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Item numbers below follow arXiv v1; the published version shifts section numbers by one (arXiv §5 = GT §6). Definition 2.27 and Remark 2.28, p. 14 of arXiv v1 (GT Definition 3.28). Transitivity is used implicitly in the proof of Theorem 1.5 (Section 5.1), where the strong isotopy of Proposition 4.2 is followed by the strong isotopy from φ₁ to ψ.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem stronglyIsotopic_trans {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {X₀ X₁ X₂ : (x : U) → TangentSpace I3 x} {φ₀ φ₁ φ₂ : U → U}
    (h₀₁ : StronglyIsotopic X₀ φ₀ X₁ φ₁) (h₁₂ : StronglyIsotopic X₁ φ₁ X₂ φ₂) :
    StronglyIsotopic X₀ φ₀ X₂ φ₂ := by sorry

end AnosovPlugs
