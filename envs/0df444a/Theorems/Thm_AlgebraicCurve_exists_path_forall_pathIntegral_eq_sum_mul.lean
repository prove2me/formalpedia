-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul
-- name    : AlgebraicCurve.exists_path_forall_pathIntegral_eq_sum_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/25ed1bbb-117e-51a5-b0c1-dfc2c7f53e43
-- title:
--   One loop realising an integer combination of periods
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, assumed to contain an element $x$ transcendental over $\mathbb{C}$ such that $F$ is finite-dimensional over the intermediate field $\mathbb{C}(x)$. Assume $F$ is a curve over $\mathbb{C}$ in the sense that every nonzero $f \in F$ has a finitely supported divisor recording the orders $v.\mathrm{ord}\,f$ and of degree $0$, each residue field of a place is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$; assume also that every nonzero $\omega \in \Omega[F/\mathbb{C}]$ has a finitely supported divisor recording the integers $v.\mathrm{ordDifferential}\,\omega$ ($=$ the order at $v$ of the coefficient of $\omega$ against $v.\mathrm{dCoord}$). The space $\mathrm{Place}\,\mathbb{C}\,F$ of places carries a topology and an analytic manifold structure charted on $\mathbb{C}$, and is compact, Hausdorff and connected. The hypothesis `hF` says that for every nonzero $f$ and every place $v$, the function $z \mapsto \mathrm{Place.evalAt}\,((\mathrm{extChartAt}\ v)^{-1} z)\, f$ is meromorphic at the chart image of $v$ with order exactly $v.\mathrm{ord}\,f$. Given a finite index type $\iota$, a finite set $T$ of places, places $P_{z,k}$, loops $Z_k$ at $P_{z,k}$ none of whose points lies in $T$, integers $m_k$, and a place $Q_0 \notin T$, the conclusion asserts the existence of a loop $\alpha$ at $Q_0$ avoiding $T$ such that for every $\theta \in \Omega[F/\mathbb{C}]$ with $v.\mathrm{ordDifferential}\,\theta \ge 0$ at all places $v \notin T$ one has $\mathrm{pathIntegral}\,\theta\,\alpha = \sum_k m_k \cdot \mathrm{pathIntegral}\,\theta\,(Z_k)$, the path integrals being defined as the increment of a primitive along the path read in charts (and $0$ when no such primitive exists).
--
--   This is the surface-topological step that replaces a finite integral combination of loop periods by the period of a single loop based at a prescribed point, obtained by concatenating conjugated powers of the given loops inside the complement of the finite set $T$, which is path-connected. It feeds the reciprocity statement [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity) for periods of differentials on the Riemann surface of places of a complex function field, and rests on the existence and uniqueness up to constants of primitives along paths provided by [`AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg`](thm.html#AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_path_forall_pathIntegral_eq_sum_mul
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {ι : Type*} [Fintype ι] (T : Finset (Place ℂ F)) {Pz : ι → Place ℂ F}
    (Z : ∀ k, Path (Pz k) (Pz k)) (hZ : ∀ k t, Z k t ∉ T) (m : ι → ℤ)
    (Q₀ : Place ℂ F) (hQ₀ : Q₀ ∉ T) :
    ∃ α : Path Q₀ Q₀, (∀ t, α t ∉ T) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
        pathIntegral θ α = ∑ k, (m k : ℂ) * pathIntegral θ (Z k) := by sorry
