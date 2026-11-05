-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_local_page_family
-- name    : FiniteEnergyPlane.exists_local_page_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:47:34.999596+00:00
-- url     : https://prove2.me/theorems/2d777368-e587-47e7-b835-41f75a8a3591
-- title:
--   Local $C^l$ families of normalized fast planes along a Reeb trajectory
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Let $y$ be a Reeb trajectory, $t_0,\gamma\in\mathbb{R}$, $u_0\in\Lambda(\{y(t_0)\},P)$ and $l\ge1$. Then there are $\varepsilon>0$ and a family $U$, of class $C^l$ on $(t_0-\varepsilon,t_0+\varepsilon)\times\mathbb{C}$, such that $U(t_0,\cdot)=u_0$ and, with $I=(t_0-\varepsilon,t_0+\varepsilon)$:
--   1. $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for every $t\in I$;
--   2. $\mathrm{pageMap}\,H\,U$ is injective on $I\times\mathbb{C}$, has injective derivative there, and avoids $x(\mathbb{R})$;
--   3. if $(v_k)$ is a sequence of embedded fast finite-energy planes asymptotic to $P$ at $\infty$ with $v_k\to u_0$ in $C^\infty_{loc}(\mathbb{C})$, then there are $A_k\to1$, $B_k\to0$ in $\mathbb{C}$ and $r_k\to0$, $t_k\to t_0$ in $\mathbb{R}$ such that, for all large $k$, $t_k\in I$ and $U(t_k,z)=(r_k\cdot v_k)(A_kz+B_k)$ for all $z\in\mathbb{C}$.
--
--   **Formalization Note** $\Lambda(\{y_0\},P)$ is `embeddedFastPlaneSet H J P {y₀} γ`, whose members satisfy $u(0)=y_0$ and have $d\lambda$-energy $\gamma$ on $\{|z|>1\}$. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated. The translation $r\cdot v$ is `shiftA r v`, $z\mapsto e^{2r}v(z)$. "$u$ is an embedding on $I\times\mathbb{C}$" of Lemma 7.3 is: injective with injective derivative, the domain and the target $S$ both having dimension $3$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemmas 7.2 and 7.3

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemmas 7.2 and 7.3. Let `P` be a periodic Reeb orbit of
Conley–Zehnder index at least `3`, `y` a Reeb trajectory and `u₀ ∈ Λ({y t₀}, P)`. For every `l ≥ 1`
there are `ε > 0` and a `C^l` family `U` on `(t₀ - ε, t₀ + ε) × ℂ` with `U(t₀, ·) = u₀` and
`U(t, ·) ∈ Λ({y t}, P)` such that:
(1) `pageMap H U` is injective with injective derivative there, and avoids `x(ℝ)`;
(2) if embedded fast finite-energy planes `vₖ` asymptotic to `P` at `∞` converge to `u₀` in
`C^∞_loc`, then there are `Aₖ → 1`, `Bₖ → 0`, `rₖ → 0` and `tₖ → t₀` such that
`U(tₖ, z) = (rₖ · vₖ)(Aₖ z + Bₖ)` for all `z` and all large `k`. -/
theorem exists_local_page_family (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (t₀ : ℝ) (u₀ : ℂ → V 1) (hu₀ : u₀ ∈ embeddedFastPlaneSet H J P {y t₀} γ)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ ε > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (ball t₀ ε) U ∧
      (∀ z, U (t₀, z) = u₀ z) ∧
      Set.InjOn (pageMap H U) (ball t₀ ε ×ˢ Set.univ) ∧
      (∀ p ∈ ball t₀ ε ×ˢ (Set.univ : Set ℂ),
        Function.Injective (fderiv ℝ (pageMap H U) p) ∧ pageMap H U p ∉ Set.range P.x) ∧
      ∀ v : ℕ → ℂ → V 1,
        (∀ k, IsFastPlane H J (v k) ∧ IsNondegenerateEnd H (v k) cylInf P 1 ∧
          IsEmbeddedPlane (v k)) →
        JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ →
        ∃ (A B : ℕ → ℂ) (r t : ℕ → ℝ), Tendsto A atTop (𝓝 1) ∧ Tendsto B atTop (𝓝 0) ∧
          Tendsto r atTop (𝓝 0) ∧ Tendsto t atTop (𝓝 t₀) ∧
          ∀ᶠ k in atTop, t k ∈ ball t₀ ε ∧
            ∀ z, U (t k, z) = shiftA (r k) (v k) (A k * z + B k) := by
  sorry

end FiniteEnergyPlane
