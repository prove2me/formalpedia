-- Prove2me | Theorems.Thm_FiniteEnergyPlane_embedded_fastPlane_fredholm
-- name    : FiniteEnergyPlane.embedded_fastPlane_fredholm
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:11:51.547984+00:00
-- url     : https://prove2.me/theorems/d101e2f0-d0a2-4aca-b55f-cdea77d2960b
-- title:
--   Fredholm theory of embedded fast finite-energy planes
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level (in the sense of `HryniewiczCriterion`), $H$ the same function on $V=\mathbb{R}^{2\cdot(1+1)}$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $P=(x,T_P)$ a periodic Reeb orbit of $H$ with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate), and $u$ an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Then $\mathrm{proj}\circ u$ does not meet $x(\mathbb{R})$ and is a proper embedding of $\mathbb{C}$ into $S\setminus x(\mathbb{R})$. Moreover, for every $l\ge1$ there are $r>0$ and a $C^l$ embedding $f:\mathbb{C}\times B_r(0)\to\mathbb{R}^4$ such that
--   1. $f(\cdot,0)=u$;
--   2. for every $\tau\in B_r(0)$, $f(\cdot,\tau)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$;
--   3. if $\tau_0\in B_r(0)$ and $(u_k)$ is a sequence of embedded fast finite-energy planes asymptotic to $P$ at $\infty$ with $u_k\to f(\cdot,\tau_0)$ in $C^\infty_{loc}(\mathbb{C})$, then there are $\tau_k\to\tau_0$, $A_k\to1$ and $B_k\to0$ in $\mathbb{C}$ such that, for all large $k$, $\tau_k\in B_r(0)$ and $f(A_kz+B_k,\tau_k)=u_k(z)$ for all $z\in\mathbb{C}$.
--
--   **Formalization Note** The level is given in the form of `exists_transverse_disk_open_book_of_approx` and of the goal of the previous mission. The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (nondegenerate in the sense of Hryniewicz 2014, Definition 2.9); "fast" is `IsFastPlane`, "embedded" is `IsEmbeddedPlane`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$; $P$ itself need not be nondegenerate. Hryniewicz writes the hypothesis as $\mu(\tilde u)\ge3$, where $\mu(\tilde u)$ is the index of $P$ in the class of trivializations of $\xi$ along $P$ that extend over the capping disk $u$. On a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so $\mu(\tilde u)$ is determined by $P$ and equals the index in that frame. Hryniewicz also requires $\mu(f(\cdot,\tau))=\mu(\tilde u)$. On a strictly star-shaped level this index depends only on the asymptotic orbit (see above), and every $f(\cdot,\tau)$ is asymptotic to $P$, so the condition is not restated. The same applies to the condition $\mu(\tilde u_n)=\mu$ in Hryniewicz's (3). The parameter $\tau$ ranges over the open ball $B_r(0)\subset\mathbb{C}$, which stands for Hryniewicz's $B_r(0)\subset\mathbb{R}^2$. "$C^l$ embedding" is: $f:\mathbb{C}\times\mathbb{C}\to\mathbb{R}^4$ is `ContDiffOn ℝ l`, injective, and has injective derivative at every point of $\mathbb{C}\times B_r(0)$. "Proper embedding of $\mathbb{C}$ into $S\setminus x(\mathbb{R})$" is stated as: $\mathrm{proj}\circ u$ is injective, its derivative is injective at every point, and $(\mathrm{proj}\circ u)^{-1}(K)$ is bounded for every compact $K\subset\mathbb{R}^4$ disjoint from $x(\mathbb{R})$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 2.3; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III: Fredholm theory, in Topics in Nonlinear Analysis, Progr. Nonlinear Differential Equations Appl. 35, Birkhäuser 1999, 381–475, doi:10.1007/978-3-0348-8765-6_18, Theorem 1.5

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Theorem 2.3. Let `S = H⁻¹(1) ⊂ ℝ⁴` be strictly star-shaped (in the
coordinates of `HryniewiczCriterion`), `J` a compatible complex structure on `ξ`, and `u` an
embedded fast finite-energy plane asymptotic to the periodic Reeb orbit `P` at `∞`, where the
Conley–Zehnder index of `P` is at least `3` (`P` may be degenerate). Then `proj H ∘ u` does not meet
`x(ℝ)` and is a proper embedding of `ℂ` into `S \ x(ℝ)`. Moreover, for every `l ≥ 1` there are
`r > 0` and a `C^l` embedding `f : ℂ × B_r(0) → V 1` such that
(1) `f(·, 0) = u`;
(2) every `f(·, τ)`, `|τ| < r`, is an embedded fast finite-energy plane asymptotic to `P` at `∞`;
(3) if `τ₀ ∈ B_r(0)` and embedded fast finite-energy planes `uₖ` asymptotic to `P` at `∞`
converge to `f(·, τ₀)` in `C^∞_loc`, then there are `τₖ → τ₀`, `Aₖ → 1` and `Bₖ → 0` with
`f(Aₖ z + Bₖ, τₖ) = uₖ(z)` for all `z` and all large `k`. -/
theorem embedded_fastPlane_fredholm (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    P.IsCZAtLeast 3 → ∀ u : ℂ → V 1, IsFastPlane H J u → IsNondegenerateEnd H u cylInf P 1 →
    IsEmbeddedPlane u →
    (∀ z, proj H (u z) ∉ Set.range P.x) ∧ (Function.Injective (proj H ∘ u) ∧
      (∀ z, Function.Injective (fderiv ℝ (proj H ∘ u) z)) ∧
      ∀ K : Set (V 1), IsCompact K → Disjoint K (Set.range P.x) →
        Bornology.IsBounded ((proj H ∘ u) ⁻¹' K)) ∧
    ∀ l : ℕ, 1 ≤ l → ∃ r > 0, ∃ f : ℂ × ℂ → V 1, ContDiffOn ℝ l f (Set.univ ×ˢ ball (0 : ℂ) r) ∧ Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p)) ∧
      (∀ z, f (z, 0) = u z) ∧
      (∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
        IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ))) ∧
      ∀ τ₀ ∈ ball (0 : ℂ) r, ∀ v : ℕ → ℂ → V 1,
        (∀ k, IsFastPlane H J (v k) ∧ IsNondegenerateEnd H (v k) cylInf P 1 ∧
          IsEmbeddedPlane (v k)) →
        JHolomorphic.TendstoCInftyLocOn v (fun z => f (z, τ₀)) Set.univ →
        ∃ τ A B : ℕ → ℂ, Tendsto τ atTop (𝓝 τ₀) ∧ Tendsto A atTop (𝓝 1) ∧
          Tendsto B atTop (𝓝 0) ∧
          ∀ᶠ k in atTop, τ k ∈ ball (0 : ℂ) r ∧ ∀ z, f (A k * z + B k, τ k) = v k z := by
  sorry

end FiniteEnergyPlane
