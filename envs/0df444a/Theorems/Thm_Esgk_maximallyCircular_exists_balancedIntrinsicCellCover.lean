-- Prove2me | Theorems.Thm_Esgk_maximallyCircular_exists_balancedIntrinsicCellCover
-- name    : Esgk.maximallyCircular_exists_balancedIntrinsicCellCover
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-16T05:09:24.691989+00:00
-- url     : https://prove2.me/theorems/4781ad3b-bd35-4540-90c4-0d19cd543a53
-- title:
--   Balanced intrinsic cell covers on a maximally circular curve
-- statement:
--   Let $G$ be an irreducible and absolutely irreducible real plane polynomial of degree $d$, with real zero set $C$. Assume that $G$ is not a circle factor and is maximally circular: its local order at each of the two complex circular points at infinity is $d/2$. Let $S\subset C$ be a finite sample with $N=|S|\ge 2$.
--
--   There is one disjoint split $S=P_1\sqcup P_2$ into nonempty sets, satisfying
--
--   $$
--   |P_1|\le 2|P_2|,\qquad |P_2|\le 2|P_1|,
--   $$
--
--   Both point sets lie on $C$. The incidence configuration uses $C$ as both carrier curves, each represented by the same irreducible degree-$d$ polynomial $G$. The real curve is neither a line nor a circle, so the line- and circle-specific normalization conditions impose no additional restriction on the split. This split is chosen independently of the scale below.
--
--   For every integer $j$ with $24d\le j$ and $jd<N$, there are a finite set of cells $\Omega$, target sets $Q_\omega\subset P_2\times P_2$, label sets $L_\omega\subset P_1\times P_1$, and an exceptional set $B\subset P_2\times P_2$ with the following properties. A label $(a,b)$ is incident with a target $(p,q)$ when $\|a-p\|^2=\|b-q\|^2$.
--
--   1. $|B|\le 4d^2N$.
--   2. Every target outside $B$ belongs to some $Q_\omega$ with $\omega\in\Omega$.
--   3. Every label incident with a target in $Q_\omega$ belongs to $L_\omega$.
--   4. $|\Omega|\le 2d^2j^2$.
--   5. $|Q_\omega|\le 4N^2/(d^2j^2)$ for every $\omega\in\Omega$.
--   6. $\sum_{\omega\in\Omega}|L_\omega|\le 20d^2jN^2$.

import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_MaximallyCircularIntrinsicCellCover
import Definitions.Def_Esgk_PachDeZeeuwQuadraticDegree
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_Esgk_PlaneNonabsoluteRealPointBound
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface

open Esgk
open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)

theorem Esgk.maximallyCircular_exists_balancedIntrinsicCellCover
    {G : PlanePoly} (hG : Irreducible G) (hAbs : IsAbsolutelyIrreducible G)
    (hNotCircle : ¬ IsCircleFactor G) (hMax : IsMaximallyCircular G)
    (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G)
    (hcard : 2 ≤ S.card) :
    ∃ X : PreparedBipartiteInput G.totalDegree,
      SelfCurvePreparedInput X ∧
      X.C₂ = PlaneCurveZeroSet G ∧
      Disjoint X.P₁ X.P₂ ∧ X.P₁ ∪ X.P₂ = S ∧
      X.P₁.card ≤ 2 * X.P₂.card ∧
      X.P₂.card ≤ 2 * X.P₁.card ∧
      0 < X.P₁.card * X.P₂.card ∧
      ∀ j : ℕ, 24 * G.totalDegree ≤ j → j * G.totalDegree < S.card →
        Nonempty (IntrinsicAuxiliaryCellCover X S.card j) := by sorry
