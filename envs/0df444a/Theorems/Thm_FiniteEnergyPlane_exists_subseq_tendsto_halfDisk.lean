-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_halfDisk
-- name    : FiniteEnergyPlane.exists_subseq_tendsto_halfDisk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:34:56.083059+00:00
-- url     : https://prove2.me/theorems/20a716d1-0739-4766-a655-240087aa5cb0
-- title:
--   $C^\infty$ compactness of pseudoholomorphic half-disks with totally real boundary
-- statement:
--   Smoothness and compactness, up to the boundary, of pseudoholomorphic maps on a half-disk whose boundary lies in a totally real subspace.
--
--   Let $E$ be a finite-dimensional real vector space, $O\subset E$ open, $J_\nu\to J$ in $C^\infty_{loc}(O)$ smooth almost complex structures on $O$, and $L\subset E$ a linear subspace with $E=L\oplus J(x)L$ for all $x\in O\cap L$. Put
--   $$D^+=\{|z|<1,\ \operatorname{Im}z\ge0\},\qquad D^+_0=\{|z|<1,\ \operatorname{Im}z>0\}.$$
--   Let $u_\nu:D^+\to E$ be of class $C^1$, $J_\nu$-holomorphic on $D^+_0$, with values in a fixed compact $K_0\subset O$, with $u_\nu(z)\in L$ for real $z$, and with first derivatives bounded on $D^+_0$ uniformly in $\nu$. Then a subsequence of $(u_\nu)$ converges in $C^\infty_{loc}(D^+)$, up to the real axis, to a smooth map $v:D^+\to K_0$ that is $J$-holomorphic on $D^+_0$.
--
--   A totally real submanifold of half dimension is locally of the form $O\cap L$ in suitable coordinates, so the statement is the local form of boundary regularity and compactness; it is independent of symplectizations.
--
--   **Formalization Note** Convergence is uniform convergence, on compact subsets of $D^+$, of all derivatives within $D^+$ (`iteratedFDerivWithin`). The sequence $u_\nu$ is only prescribed on $D^+$.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorems 22, 23 and 24

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Theorems 22–24, in local form. Let `J_ν → J` in `C^∞_loc` be smooth almost complex structures
on an open set `O` of a finite-dimensional real vector space `E`, and `L ⊆ E` a linear subspace with
`E = L ⊕ J(x) L` for every `x ∈ O ∩ L`. Put `D⁺ = {|z| < 1, Im z ≥ 0}`. Every sequence of maps
`u_ν`, `C¹` on `D⁺`, `J_ν`-holomorphic in its interior, with values in a fixed compact `K₀ ⊆ O`,
with `u_ν(z) ∈ L` for real `z`, and with uniformly bounded first derivative, has a subsequence converging in
`C^∞_loc` on `D⁺` (up to the real axis) to a `C^∞` map `v` on `D⁺` that is `J`-holomorphic in the interior. -/
theorem exists_subseq_tendsto_halfDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (hJν : ∀ ν, JHolomorphic.IsAlmostComplexOn (Jν ν) O)
    (hconv : JHolomorphic.TendstoCInftyLocOn Jν J O) (L : Submodule ℝ E)
    (hL : ∀ x ∈ O, x ∈ L → IsCompl L (L.map (J x : E →ₗ[ℝ] E)))
    (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O) (u : ℕ → ℂ → E) :
    let D : Set ℂ := {z | ‖z‖ < 1 ∧ 0 ≤ z.im}
    let D₀ : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}
    (∀ ν, ContDiffOn ℝ 1 (u ν) D) → (∀ ν, JHolomorphic.IsJHolomorphicOn (Jν ν) D₀ (u ν)) →
    (∀ ν, Set.MapsTo (u ν) D K₀) → (∀ ν, ∀ z ∈ D, z.im = 0 → u ν z ∈ L) →
    (∃ C : ℝ, ∀ ν, ∀ z ∈ D₀, ‖fderiv ℝ (u ν) z‖ ≤ C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → E, ContDiffOn ℝ ∞ v D ∧
      JHolomorphic.IsJHolomorphicOn J D₀ v ∧ Set.MapsTo v D K₀ ∧
      ∀ K ⊆ D, IsCompact K → ∀ m : ℕ, TendstoUniformlyOn
        (fun ν => iteratedFDerivWithin ℝ m (u (φ ν)) D) (iteratedFDerivWithin ℝ m v D) atTop K := by
  sorry

end FiniteEnergyPlane
