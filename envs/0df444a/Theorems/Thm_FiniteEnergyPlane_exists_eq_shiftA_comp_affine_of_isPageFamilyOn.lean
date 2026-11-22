-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eq_shiftA_comp_affine_of_isPageFamilyOn
-- name    : FiniteEnergyPlane.exists_eq_shiftA_comp_affine_of_isPageFamilyOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T18:05:24.771092+00:00
-- url     : https://prove2.me/theorems/2e91fe67-f6c2-41be-af8d-898fff1ff3bd
-- title:
--   Nearby embedded fast planes are slices of a family of normalized fast planes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate). Let $y$ be a Reeb trajectory, $\gamma\in\mathbb{R}$, $l\ge1$, $I\subseteq\mathbb{R}$ open, $U$ a family of class $C^l$ on $I\times\mathbb{C}$ with $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for every $t\in I$, and $t_0\in I$. If $(v_k)$ is a sequence of embedded fast finite-energy planes asymptotic to $P$ at $\infty$ with $v_k\to U(t_0,\cdot)$ in $C^\infty_{loc}(\mathbb{C})$, then there are $A_k\to1$, $B_k\to0$ in $\mathbb{C}$ and $r_k\to0$, $t_k\to t_0$ in $\mathbb{R}$ such that, for all large $k$, $t_k\in I$ and $U(t_k,z)=(r_k\cdot v_k)(A_kz+B_k)$ for every $z\in\mathbb{C}$.
--
--   This is property (3) of Hryniewicz's Lemma 7.3, stated for an arbitrary family through the limit plane: every plane close to a slice of the family is, up to an $\mathbb{R}$-translation and an affine change of the domain, a nearby slice.
--
--   **Formalization Note** $\Lambda(\{y_0\},P)$ is `embeddedFastPlaneSet H J P {y₀} γ`, whose members satisfy $u(0)=y_0$ and have $d\lambda$-energy $\gamma$ on $\{|z|>1\}$. The family conditions are `IsPageFamilyOn H J P γ y l I U`. The translation $r\cdot v$ is `shiftA r v`, $z\mapsto e^{2r}v(z)$. "Asymptotic to $P$ at $\infty$" is `IsNondegenerateEnd H v cylInf P 1`, and $C^\infty_{loc}$ convergence is `JHolomorphic.TendstoCInftyLocOn v (U(t₀, ·)) Set.univ`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`. Hryniewicz also assumes $\mu(v_k)=k$; on a strictly star-shaped level this is automatic, as in the parent statement.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.3 (3)

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 7.3 (3), for an arbitrary family. Let `P` be a periodic
Reeb orbit of Conley–Zehnder index at least `3`, `y` a Reeb trajectory, `I ⊆ ℝ` open, `U` a `C^l`
family (`l ≥ 1`) on `I × ℂ` with `U(t, ·) ∈ Λ({y t}, P)` for `t ∈ I`, and `t₀ ∈ I`. If embedded
fast finite-energy planes `vₖ` asymptotic to `P` at `∞` converge to `U(t₀, ·)` in `C^∞_loc`, then
there are `Aₖ → 1`, `Bₖ → 0`, `rₖ → 0` and `tₖ → t₀` such that, for all large `k`, `tₖ ∈ I` and
`U(tₖ, z) = (rₖ · vₖ)(Aₖ z + Bₖ)` for every `z`. -/
theorem exists_eq_shiftA_comp_affine_of_isPageFamilyOn (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t₀ : ℝ) (ht₀ : t₀ ∈ I) (v : ℕ → ℂ → V 1)
    (hv : ∀ k, IsFastPlane H J (v k) ∧ IsNondegenerateEnd H (v k) cylInf P 1 ∧
      IsEmbeddedPlane (v k))
    (hvlim : JHolomorphic.TendstoCInftyLocOn v (fun z => U (t₀, z)) Set.univ) :
    ∃ (A B : ℕ → ℂ) (r t : ℕ → ℝ), Tendsto A atTop (𝓝 1) ∧ Tendsto B atTop (𝓝 0) ∧
      Tendsto r atTop (𝓝 0) ∧ Tendsto t atTop (𝓝 t₀) ∧
      ∀ᶠ k in atTop, t k ∈ I ∧ ∀ z, U (t k, z) = shiftA (r k) (v k) (A k * z + B k) := by
  sorry

end FiniteEnergyPlane
