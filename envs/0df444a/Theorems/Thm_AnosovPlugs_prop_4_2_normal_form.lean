-- Prove2me | Theorems.Thm_AnosovPlugs_prop_4_2_normal_form
-- name    : AnosovPlugs.prop_4_2_normal_form
-- status  : Open
-- author  : @ebayuser
-- created : 2026-10-02T10:12:22.484207+00:00
-- url     : https://prove2.me/theorems/798ad5b9-096a-49c8-980c-c3e002b8e379
-- title:
--   Proposition 4.2 (Béguin–Bonatti–Yu): normal form of a saddle hyperbolic plug with a strongly transverse gluing map
-- statement:
--   Let $(U,X)$ be a hyperbolic plug with filling MS laminations whose maximal invariant set $\Lambda_X$ contains neither attractors nor repellers (a *saddle* hyperbolic plug, Definition 4.1), and let $\varphi:\partial^{out}U\to\partial^{in}U$ be a strongly transverse gluing diffeomorphism.
--
--   Then there exist a vector field $Y$ on $U$ and a map $\varphi_1:\partial^{out}U\to\partial^{in}U$ such that
--
--   1. $(U,Y)$ is a hyperbolic plug with filling MS laminations whose maximal invariant set $\Lambda_Y$ contains neither attractors nor repellers, $\varphi_1$ is a strongly transverse gluing map for $(U,Y)$, and $(U,Y,\varphi_1)$ is strongly isotopic to $(U,X,\varphi)$;
--   2. there exist smooth $Y$-invariant foliations $\mathcal G^s$ and $\mathcal G^u$ of $U$, transverse to each other, such that $W^s(\Lambda_Y)$ is a sublamination of $\mathcal G^s$ and $W^u(\Lambda_Y)$ is a sublamination of $\mathcal G^u$. Write $\mathcal G^s_{in},\mathcal G^u_{in}$ and $\mathcal G^s_{out},\mathcal G^u_{out}$ for the one-dimensional foliations they induce on $\partial^{in}U$ and $\partial^{out}U$;
--   3. for each compact leaf of $\mathcal G^u_{out}$ and of $\mathcal G^s_{in}$ the holonomy is conjugated to a homothety;
--   4. the image $(\varphi_1)_*\mathcal G^u_{out}$ is transverse to $\mathcal G^s_{in}$.
--
--   $$ (U,X,\varphi)\ \text{saddle, filling, strongly transverse}\ \Longrightarrow\ \exists\,(U,Y,\varphi_1)\ \text{strongly isotopic, in normal form}. $$
--
--   This is the first step of the proof of Theorem 1.5: it provides the invariant foliations along which the return map of the glued flow is controlled, and the affine (homothetic) holonomies that the distortion estimates of Section 5 require.
--
--   **Formalization Note** The clause "$Y$ arbitrarily $C^1$-close to $X$" of the paper is not stated; Theorem 1.5 only uses the strong isotopy. Foliations are given by foliated atlases of smooth charts whose transition maps preserve the third coordinate (`IsFoliatedAtlas3`); $Y$-invariance means that every orbit segment stays in the leaf of its initial point; "sublamination" means that the leaf of $\mathcal G^s$ through a point $p\in\Lambda_Y$ is the weak stable set of $p$; the holonomy condition is stated with a $C^1$ conjugating diffeomorphism of a transverse arc and a ratio $\mu\neq0$, $|\mu|\neq1$, negative for one-sided compact leaves (`HasHomotheticHolonomy`); transversality of $(\varphi_1)_*\mathcal G^u_{out}$ and $\mathcal G^s_{in}$ is pointwise transversality of leaves (`CurvesTransverseAt`). The package of items 2 to 4 is the predicate `IsNormalForm`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Item numbers below follow arXiv v1; the published version shifts section numbers by one (arXiv §5 = GT §6). Proposition 4.2, p. 18 of arXiv v1 (Section 4, Normal form).

import Mathlib
import Definitions.Def_AnosovPlugs_Section5

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem prop_4_2_normal_form {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (X : (x : U) → TangentSpace I3 x) (φ : U → U)
    (hX : IsFillingHyperbolicPlug X) (hXnoAR : NoAttractorNorRepeller X)
    (hφ : IsStronglyTransverseGluing X φ) :
    ∃ (Y : (x : U) → TangentSpace I3 x) (φ₁ : U → U),
      IsFillingHyperbolicPlug Y ∧ NoAttractorNorRepeller Y ∧ IsStronglyTransverseGluing Y φ₁ ∧
      StronglyIsotopic X φ Y φ₁ ∧
      ∃ As Au : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3)), IsNormalForm Y φ₁ As Au := by sorry

end AnosovPlugs
