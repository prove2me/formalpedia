-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw
-- name    : AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/cf7b9c58-be47-5362-a6b2-a12ba78d90f0
-- title:
--   Raw form of Riemann's bilinear relations
-- statement:
--   Let $F$ be a field that is a $\mathbb{C}$-algebra, assumed (via `hfg`) to contain an element transcendental over $\mathbb{C}$ over whose generated subfield $F$ is finite-dimensional, with `IsCurveOver ℂ F` (principal divisors, residue fields finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ free of rank one over $F$), `HasCanonicalDivisor` (each nonzero differential has a divisor recording $v\mapsto v.\mathrm{ordDifferential}$), and the space of places carrying a compact, Hausdorff, connected charted analytic one-dimensional complex manifold structure; `hF` requires that for every $f\neq 0$ and place $v$ the function $z\mapsto \mathrm{evalAt}$ of $f$ at the chart preimage of $z$ be meromorphic at the chart image of $v$ of meromorphic order $v.\mathrm{ord}\,f$. Given a $\mathbb{C}$-basis $b$ indexed by $\mathrm{Fin}\ n$ of the regular differentials (those $\omega$ with $\omega=f\cdot v.\mathrm{dCoord}$, $f$ in the valuation subring, at every $v$), a place $P_0$ and a finite set $S$ of places, the conclusion asserts the existence of base points $Pz$ indexed by $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, loops $Z_k$ at $Pz_k$, and an integer matrix $Q$ on that index set such that: every $Z_k$ avoids $S$ and $P_0$ pointwise; $Q^{\mathsf T}=-Q$ and $\det Q$ is a unit in $\mathbb{Z}$; for every place $P$ and loop $\delta$ at $P$ there are integers $\kappa_k$ with $\int_\delta\xi=\sum_k\kappa_k\int_{Z_k}\xi$ simultaneously for all regular $\xi$; for every loop $\delta$ avoiding $S$ there are integers $\kappa_k$ and integer weights $w$ on places such that for every $\theta\in\Omega[F/\mathbb{C}]$ with $v.\mathrm{ordDifferential}\,\theta\ge -1$ everywhere and $\ge 0$ off $S$ one has $\int_\delta\theta=\sum_k\kappa_k\int_{Z_k}\theta+2\pi i\sum_{v\in S}w_v\,\mathrm{evalAt}_v(v.\mathrm{dCoordFn}\cdot v.\mathrm{differentialCoeff}\,\theta)$; $\sum_{k,l}Q_{kl}\int_{Z_k}\xi\int_{Z_l}\xi'=0$ for all regular $\xi,\xi'$; and for every divisor $E$ and $\theta$ with $v.\mathrm{ordDifferential}\,\theta\ge -1$ everywhere, with $\mathrm{evalAt}_v(v.\mathrm{dCoordFn}\cdot v.\mathrm{differentialCoeff}\,\theta)=E(v)$ for all $v$ and $E$ supported in $S$, there are integers $\kappa_k$ with $\sum_{k,l}Q_{kl}\int_{Z_k}b_i\int_{Z_l}\theta=2\pi i\bigl(\mathrm{abelJacobiDiv}(b,P_0)(E)_i+\sum_k\kappa_k\int_{Z_k}b_i\bigr)$ for every $i$, the integers $\kappa$ being independent of $i$. Here path integrals are the endpoint difference of a primitive along the path when one exists, and $\mathrm{abelJacobiDiv}$ is the additive extension to divisors of $v\mapsto$ integration of the $b_i$ along a chosen path from $P_0$ to $v$.
--
--   This is Riemann's bilinear relations together with the reciprocity law relating differentials of the first and third kind, stated for the unnormalised system of $2n$ loops produced by a single dissection of the surface rather than for a symplectic homology basis. It feeds [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity), where the alternating unimodular matrix $Q$ is brought to symplectic normal form and the loops are correspondingly recombined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.lean

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

theorem AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw
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
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (S : Finset (Place ℂ F)) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
      (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
      (∀ k t, Z k t ∉ S ∧ Z k t ≠ P₀) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (P : Place ℂ F) (δ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ = ∑ k, ((κ k : ℂ) * pathIntegral ξ (Z k))) ∧
      (∀ (P : Place ℂ F) (δ : Path P P), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ k, ((κ k : ℂ) * pathIntegral θ (Z k)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral ξ (Z k) * pathIntegral ξ' (Z l) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
          ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k) * pathIntegral θ (Z l) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ k, ((κ k : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k)))) := by sorry
