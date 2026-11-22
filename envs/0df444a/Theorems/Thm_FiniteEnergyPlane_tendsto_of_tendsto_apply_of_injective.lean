-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendsto_of_tendsto_apply_of_injective
-- name    : FiniteEnergyPlane.tendsto_of_tendsto_apply_of_injective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T18:59:19.138574+00:00
-- url     : https://prove2.me/theorems/2388a112-683e-4630-99f2-597f90f3350d
-- title:
--   Convergence of arguments from convergence of values under injective linear limits
-- statement:
--   Let $F$ be a real normed space, $M:\mathbb{C}\to F$ an injective $\mathbb{R}$-linear map, and $M_k:\mathbb{C}\to F$ continuous $\mathbb{R}$-linear maps with $M_k\to M$ in operator norm. If $a_k\in\mathbb{C}$ and $b\in\mathbb{C}$ satisfy $M_k a_k\to Mb$, then $a_k\to b$.
--
--   A general fact used to identify limits of reparametrization constants from derivatives, for example for families of finite-energy planes (Hryniewicz 2012, Lemma 7.3).
--
--   **Formalization Note** Operator-norm convergence is `Tendsto Mk atTop (𝓝 M)` in `ℂ →L[ℝ] F`.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemmas 7.2 and 7.3

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology

/-- Let `M : ℂ →L[ℝ] F` be injective and `Mₖ → M` in operator norm. If `Mₖ aₖ → M b`, then
`aₖ → b`. -/
theorem tendsto_of_tendsto_apply_of_injective {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : ℂ →L[ℝ] F) (hM : Function.Injective M) (Mk : ℕ → ℂ →L[ℝ] F)
    (hMk : Tendsto Mk atTop (𝓝 M)) (a : ℕ → ℂ) (b : ℂ)
    (hlim : Tendsto (fun k => Mk k (a k)) atTop (𝓝 (M b))) :
    Tendsto a atTop (𝓝 b) := by
  sorry

end FiniteEnergyPlane
