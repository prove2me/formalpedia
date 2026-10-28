-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_plane_of_gradNorm_le
-- name    : FiniteEnergyPlane.exists_plane_of_gradNorm_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T17:56:20.291591+00:00
-- url     : https://prove2.me/theorems/62f51adf-19f9-4c63-8393-a5dda89582f3
-- title:
--   A nonconstant finite-energy plane from curves with normalized gradients on growing discs
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, with associated almost complex structure $\tilde J$. Let $\rho_k\to\infty$ and let $v_k$ be finite-energy $\tilde J$-holomorphic curves on the discs $B(0,\rho_k)$ such that, for all $k$,
--   - $E(v_k)\le C$ (Hofer energy on $B(0,\rho_k)$);
--   - $|\nabla v_k(z)|\le 2$ for $z\in B(0,\rho_k)$;
--   - $a(v_k(0))=0$ and $|\nabla v_k(0)|=1$.
--
--   Then there are a subsequence $(v_{k_j})$ and a nonconstant finite-energy $\tilde J$-holomorphic plane $w:\mathbb C\to\mathbb R^{2n+2}\setminus\{0\}$ with $E(w)\le C$ such that for every $R$
--   $$\int_{B(0,R)}w^*d\lambda\ \le\ \liminf_{j\to\infty}\int_{B(0,R)}v_{k_j}^*d\lambda .$$
--
--   This produces the plane that bubbles off at a point of gradient blow-up, together with the lower semicontinuity of the $d\lambda$-energy needed to compare it with the curves it comes from.
--
--   **Formalization Note** $|\nabla v|$ is the $\mathbb R$-invariant norm `gradNorm H v` $=\|D(a\circ v)\|+\|D(\mathrm{proj}\circ v)\|$ and $a$ is `aCoord H`. "Finite-energy curve" is `IsFiniteEnergyCurve` (smooth, avoids $0$, $\tilde J$-holomorphic, finite Hofer energy); for $w$ it is required on all of $\mathbb C$. Nonconstant means $w(z_1)\ne w(z_2)$ for some $z_1,z_2$. The $d\lambda$-energies are `dlambdaEnergy`, valued in $[0,\infty]$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, proof of Lemma 2.20, p. 12; H. Hofer, Invent. Math. 114 (1993), Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A bubble plane from curves with normalized gradients on growing discs (Hofer 1993, p. 535;
Hryniewicz 2014, p. 12). Let `ρ_k → ∞` and let `v_k` be finite-energy `J̃`-holomorphic curves on
`B(0, ρ_k)` with Hofer energy `≤ C`, `|∇v_k| ≤ 2` on `B(0, ρ_k)` in the `ℝ`-invariant norm
`gradNorm`, `a(v_k(0)) = 0` and `|∇v_k(0)| = 1`. Then there are a subsequence `v_{k_j}` and a
nonconstant finite-energy `J̃`-holomorphic plane `w : ℂ → V` with Hofer energy `≤ C` such that,
for every `R`, the `dλ`-energy of `w` on `B(0, R)` is at most the `liminf` of the `dλ`-energies
of the `v_{k_j}` on `B(0, R)`. -/
theorem exists_plane_of_gradNorm_le {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (v : ℕ → ℂ → V n)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (hv : ∀ k, IsFiniteEnergyCurve H J (ball 0 (ρ k)) (v k))
    (C : ℝ) (hC : ∀ k, energy H (ball 0 (ρ k)) (v k) ≤ ENNReal.ofReal C)
    (hgrad : ∀ k, ∀ z ∈ ball (0 : ℂ) (ρ k), gradNorm H (v k) z ≤ 2)
    (ha0 : ∀ k, aCoord H (v k 0) = 0) (hg0 : ∀ k, gradNorm H (v k) 0 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J Set.univ w ∧
      (∃ z₁ z₂, w z₁ ≠ w z₂) ∧ energy H Set.univ w ≤ ENNReal.ofReal C ∧
      ∀ R : ℝ, dlambdaEnergy H (ball 0 R) w ≤
        liminf (fun j => dlambdaEnergy H (ball 0 R) (v (φ j))) atTop := by
  sorry

end FiniteEnergyPlane
