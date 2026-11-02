-- Prove2me | Theorems.Thm_EthierKurtz_oblique_density_from_global_solution
-- name    : EthierKurtz.oblique_density_from_global_solution
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:14:16.483919+00:00
-- url     : https://prove2.me/theorems/c515e640-3ef4-4217-94cb-1153b5f87aa9
-- title:
--   Dense range of the oblique resolvent from global Schauder solvability
-- statement:
--   Let $\Omega$ be bounded and open, $0<\mu\le1$, and suppose that $\bar a,\bar b$ agree with $a,b$ on $\Omega$ and that the oblique problem $\lambda u-\tfrac12\bar a:D^2u-\nabla u\cdot\bar b=g$, $\nabla u\cdot c=0$ is solvable with $u,Du,D^2u$ bounded and $\mu$-Hoelder on $\overline\Omega$ for all large $\lambda$ and all bounded $\mu$-Hoelder $g$ (hypothesis hG). Then there is $\lambda_0>0$ such that $\{\lambda_0 f-g : (f,g)\in\overline{\mathrm{graph}}\}$ is dense in $C(\overline\Omega)$: $$\forall h,\ \forall\delta>0,\ \exists (f,g)\in\overline{\texttt{obliqueDiffusionGraph}\,\Omega\,\mu\,a\,b\,c},\quad \|\lambda_0 f-g-h\|<\delta.$$
--
--   Role: turns Schauder solvability into the dense-range condition of the Hille-Yosida theorem (Hoelder functions are dense in $C(\overline\Omega)$).
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Theorem 6.31

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_ComponentHolder
open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_density_from_global_solution (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (a abar : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (b bbar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hG : (∃ lam1 : ℝ, 1 ≤ lam1 ∧ ∀ lam : ℝ, lam1 ≤ lam → ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ),
      (0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ closure Ω, |g x| ≤ M) ∧
        ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
      ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
        (∀ x ∈ Ω, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
        (∀ x ∈ frontier Ω, u1 x (c x) = 0) ∧
        (∀ x ∈ closure Ω, lam * u x -
          (1 / 2 : ℝ) * ∑ i, ∑ j, abar x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
            - u1 x (bbar x) = g x) ∧
        (∃ B : ℝ, ∀ x ∈ closure Ω, |u x| ≤ B ∧ ‖u1 x‖ ≤ B ∧ ‖u2 x‖ ≤ B) ∧
        (∃ B : ℝ, ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |u x - u y| ≤ B * ‖x - y‖ ^ μ ∧
          ‖u1 x - u1 y‖ ≤ B * ‖x - y‖ ^ μ ∧ ‖u2 x - u2 y‖ ≤ B * ‖x - y‖ ^ μ)))
    (heqab : ∀ x ∈ Ω, abar x = a x ∧ bbar x = b x) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : BoundedContinuousFunction (closure Ω) ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ closure (EthierKurtz.obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by sorry

end EthierKurtz
