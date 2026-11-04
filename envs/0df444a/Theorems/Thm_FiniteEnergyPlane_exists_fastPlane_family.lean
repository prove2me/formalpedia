-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_family
-- name    : FiniteEnergyPlane.exists_fastPlane_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:09:08.78829+00:00
-- url     : https://prove2.me/theorems/7d272bc2-e7fe-4515-9485-c72551bcb028
-- title:
--   Families of embedded fast planes through an embedded fast plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate) and $u$ an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Then for every $l\ge1$ there are $r>0$ and a $C^l$ embedding $f:\mathbb{C}\times B_r(0)\to\mathbb{R}^4$ such that
--   1. $f(\cdot,0)=u$;
--   2. for every $\tau\in B_r(0)$, $f(\cdot,\tau)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$;
--   3. for every sequence $c_k\to0$ in $\mathbb{R}$ there are $\tau_k\to0$ such that, for all large $k$, $\tau_k\in B_r(0)$ and the image of the translation $c_k\cdot u$ equals the image of $f(\cdot,\tau_k)$.
--
--   **Formalization Note** The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (nondegenerate in the sense of Hryniewicz 2014, Definition 2.9); "fast" is `IsFastPlane`, "embedded" is `IsEmbeddedPlane`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$; $P$ itself need not be nondegenerate. Hryniewicz writes the hypothesis as $\mu(\tilde u)\ge3$, where $\mu(\tilde u)$ is the index of $P$ in the class of trivializations of $\xi$ along $P$ that extend over the capping disk $u$. On a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so $\mu(\tilde u)$ is determined by $P$ and equals the index in that frame. Hryniewicz also requires $\mu(f(\cdot,\tau))=\mu(\tilde u)$. On a strictly star-shaped level this index depends only on the asymptotic orbit (see above), and every $f(\cdot,\tau)$ is asymptotic to $P$, so the condition is not restated. The parameter $\tau$ ranges over the open ball $B_r(0)\subset\mathbb{C}$, which stands for Hryniewicz's $B_r(0)\subset\mathbb{R}^2$. "$C^l$ embedding" is: $f:\mathbb{C}\times\mathbb{C}\to\mathbb{R}^4$ is `ContDiffOn ℝ l`, injective, and has injective derivative at every point of $\mathbb{C}\times B_r(0)$. The translation $c\cdot u$ is `shiftA c u`, $z\mapsto e^{2c}u(z)$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemmas 6.10 and 6.20; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III: Fredholm theory, in Topics in Nonlinear Analysis, Progr. Nonlinear Differential Equations Appl. 35, Birkhäuser 1999, 381–475, doi:10.1007/978-3-0348-8765-6_18, Theorems 1.5 and 5.7

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemmas 6.10 and 6.20. Let `u` be an embedded fast finite-energy
plane asymptotic to `P` at `∞`, where the Conley–Zehnder index of `P` is at least `3`. Then for
every `l ≥ 1` there are `r > 0` and a `C^l` embedding `f : ℂ × B_r(0) → V 1` (injective, with
injective derivative) such that `f(·, 0) = u`, and every `f(·, τ)`, `|τ| < r`, is an embedded fast
finite-energy plane asymptotic to `P` at `∞`. Moreover the family contains the small translations
of `u`: if `cₖ → 0` then there are `τₖ → 0` such that, for all large `k`, the image of `cₖ · u`
is the image of `f(·, τₖ)`. -/
theorem exists_fastPlane_family (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ f : ℂ × ℂ → V 1, ContDiffOn ℝ l f (Set.univ ×ˢ ball (0 : ℂ) r) ∧ Set.InjOn f (Set.univ ×ˢ ball (0 : ℂ) r) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) r, Function.Injective (fderiv ℝ f p)) ∧
      (∀ z, f (z, 0) = u z) ∧
      (∀ τ ∈ ball (0 : ℂ) r, IsFastPlane H J (fun z => f (z, τ)) ∧
        IsNondegenerateEnd H (fun z => f (z, τ)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => f (z, τ))) ∧
      ∀ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) → ∃ τ : ℕ → ℂ, Tendsto τ atTop (𝓝 0) ∧
        ∀ᶠ k in atTop, τ k ∈ ball (0 : ℂ) r ∧
          Set.range (shiftA (c k) u) = Set.range (fun z => f (z, τ k)) := by
  sorry

end FiniteEnergyPlane
