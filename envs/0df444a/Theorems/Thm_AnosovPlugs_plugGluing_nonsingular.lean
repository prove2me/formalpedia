-- Prove2me | Theorems.Thm_AnosovPlugs_plugGluing_nonsingular
-- name    : AnosovPlugs.plugGluing_nonsingular
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T17:14:22.752398+00:00
-- url     : https://prove2.me/theorems/ea15ba49-b4af-46f2-8ab1-7e4ddea1aa6c
-- title:
--   Gluing plugs (Béguin–Bonatti–Yu, Prop. 1.1): the induced vector field is nonsingular
-- statement:
--   Let $X$ and $Y$ be nonsingular vector fields on the 3-manifolds $U$ and $V$ and let $(W,Z)$ be a gluing of $(U,X)$ and $(V,Y)$ along $\varphi:T^{out}\to T^{in}$: C¹ embeddings $i_U:U\to W$ and $i_V:V\to W$ with injective derivatives cover $W$, identify exactly the points $x\in T^{out}$ with $\varphi(x)$, and satisfy $Di_U(X)=Z\circ i_U$, $Di_V(Y)=Z\circ i_V$. Then the induced vector field $Z$ is nonsingular:
--   $$ Z(w)\neq 0\quad\text{for every } w\in W. $$
--
--   This is the first half of the claim "$(W,Z)$ is a plug" in the proof of Proposition 1.1. Every point of $W$ is $i_U(x)$ or $i_V(y)$, and the derivative of an embedding is injective, so $Z(i_U(x))=Di_U(X(x))\neq0$.
--
--   **Formalization Note** Only nonsingularity of $X$ and $Y$ is assumed, not the full plug hypotheses, so the statement applies to any gluing of two vector fields in the sense of `IsPlugGluing`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1), proof of Proposition 1.1, Section 3.1 of arXiv v1 (= Section 4.1 of the published version), p. 14 of arXiv v1. First sentence of the proof: 'The vector field Z is transverse to the boundary of W; hence (W,Z) is a plug' (a plug is nonsingular by Definition 2.1).

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem plugGluing_nonsingular
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U] [IsManifold I3 ∞ U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V] [IsManifold I3 ∞ V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W] [IsManifold I3 ∞ W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : ∀ x, X x ≠ 0) (hY : ∀ y, Y y ≠ 0)
    (Tout : Set U) (φ : U → V)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    ∀ w, Z w ≠ 0 := by sorry

end AnosovPlugs
