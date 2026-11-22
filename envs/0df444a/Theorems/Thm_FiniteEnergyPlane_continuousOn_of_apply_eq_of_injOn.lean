-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousOn_of_apply_eq_of_injOn
-- name    : FiniteEnergyPlane.continuousOn_of_apply_eq_of_injOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T11:38:12.897615+00:00
-- url     : https://prove2.me/theorems/39393b31-e0d2-4eaa-9ae4-74991ce24af1
-- title:
--   Continuity of a solution curve of a parametrized equation with compact injective fibres
-- statement:
--   Let $E$ be a Hausdorff topological space, $S\subset\mathbb{R}$ and $K\subset\mathbb{C}$ compact. Let $F:\mathbb{R}\times\mathbb{C}\to E$ be continuous on $S\times K$ and $g:\mathbb{R}\to E$ continuous on $S$. Let $\rho:\mathbb{R}\to\mathbb{C}$ satisfy $\rho(t)\in K$ and
--   $$F(t,\rho(t))=g(t)\qquad (t\in S),$$
--   and suppose that for every $t\in S$ the map $w\mapsto F(t,w)$ is injective on $K$. Then $\rho$ is continuous on $S$.
--
--   Role: a curve of solutions of a parametrized equation, constrained to a compact set on which the equation has at most one solution for each parameter, is automatically continuous; no choice of the solutions is involved. A typical use is the curve of preimages $\rho(t)\in K$ of points $g(t)$ under a continuous family of maps $F(t,\cdot)$ that are injective on $K$.
--
--   **Formalization Note** "Continuous on $S$" is `ContinuousOn ρ S`; injectivity on $K$ is `Set.InjOn (fun w => F (t, w)) K`.
-- source:
--   General analysis lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.4

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology

/-- Let `K ⊆ ℂ` be compact, `F : ℝ × ℂ → E` continuous on `S × K` and `g : ℝ → E` continuous on
`S` (`E` Hausdorff). If `ρ : ℝ → ℂ` takes values in `K` on `S`, satisfies `F (t, ρ t) = g t`, and
every `w ↦ F (t, w)` (`t ∈ S`) is injective on `K`, then `ρ` is continuous on `S`. -/
theorem continuousOn_of_apply_eq_of_injOn {E : Type*} [TopologicalSpace E] [T2Space E]
    {S : Set ℝ} {K : Set ℂ} (hK : IsCompact K) {F : ℝ × ℂ → E} {g : ℝ → E} {ρ : ℝ → ℂ}
    (hF : ContinuousOn F (S ×ˢ K)) (hg : ContinuousOn g S) (hρK : ∀ t ∈ S, ρ t ∈ K)
    (heq : ∀ t ∈ S, F (t, ρ t) = g t) (hinj : ∀ t ∈ S, Set.InjOn (fun w => F (t, w)) K) :
    ContinuousOn ρ S := by
  sorry

end FiniteEnergyPlane
