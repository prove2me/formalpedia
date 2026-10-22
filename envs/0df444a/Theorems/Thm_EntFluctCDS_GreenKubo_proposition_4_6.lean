-- Prove2me | Theorems.Thm_EntFluctCDS_GreenKubo_proposition_4_6
-- name    : EntFluctCDS.GreenKubo.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:43.290313+00:00
-- url     : https://prove2.me/theorems/6feda65d-d481-42c4-8c51-146851ec49c7
-- title:
--   Proposition 4.6 — finite-time Green–Kubo formula and Onsager reciprocity
-- statement:
--   Let $(M,\phi_X,\omega_X,\Phi_X)$ be a regular family with a positive number of force coordinates. Assume (T1), stationarity of $\omega_0$ under $\phi_0$, and (T2), time reversal with odd flux for every $X$. Fix $t>0$. Suppose that every equilibrium flux coordinate belongs to $L^2(\omega_0)$, that the $X$-system flux is integrable over $[0,t]\times M$ for $X$ near zero, and that the actual log-Laplace functional $g_t(X,Y)$ is finite and $C^{1,2}$ near $(0,0)$. Define $\langle\Phi_X\rangle_t=t^{-1}\int_0^t\omega_X(\Phi_X\circ\phi_X^s)\,ds$ and $L_{jkt}=\left.\partial_{X_k}\langle\Phi_X^{(j)}\rangle_t\right|_{X=0}$. Then $X\mapsto\langle\Phi_X\rangle_t$ is differentiable at zero, and for all $j,k$,
--
--   $$L_{jkt}=\frac12\int_{-t}^{t}\omega_0\!\left(\Phi_0^{(k)}\,\Phi_0^{(j)}\circ\phi_0^s\right)\left(1-\frac{|s|}{t}\right)ds,\qquad L_{jkt}=L_{kjt}.$$
--
--   The first identity expresses finite-time response through equilibrium flux correlations; the second is finite-time Onsager reciprocity.
--
--   **Formalization Note** The two integrability conditions state the moment and Fubini requirements used on p. 21. The local $C^{1,2}$ condition comprises exactly the five derivative families defined on p. 19. The time average uses the state and flow of each $X$-system, while the correlation uses the equilibrium system.
-- source:
--   Jakšić, Pillet & Rey-Bellet, Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, pp. 20–21, Proposition 4.6, (4.31)–(4.32) and proof

import Mathlib
import Definitions.Def_EntFluctCDS_GreenKubo_Family

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace EntFluctCDS.GreenKubo

/-- Proposition 4.6, p. 20: T3, finite-time Green–Kubo, and Onsager
reciprocity. The displayed integrability conditions make the paper's
implicit expectation and Fubini steps well-defined. -/
theorem proposition_4_6 {N : ℕ} {M : Type*} [MeasurableSpace M]
    (F : Family N M) (hT1 : T1 F) (hT2 : T2 F)
    (t : ℝ) (ht : 0 < t)
    (hL2 : ∀ j : Fin N,
      MemLp (fun x : M => F.flux 0 x j) 2 ((F.sys 0).omega : Measure M))
    (U : Set (Fin N → ℝ)) (hU : U ∈ 𝓝 (0 : Fin N → ℝ))
    (hFubini : FluxIntegrableNear F t U)
    (O : Set ((Fin N → ℝ) × (Fin N → ℝ)))
    (hopen : IsOpen O) (hzero : ((0 : Fin N → ℝ), (0 : Fin N → ℝ)) ∈ O)
    (hfinite : ∀ p ∈ O, gesFunctional F t p.1 p.2 ≠ ⊥ ∧
      gesFunctional F t p.1 p.2 ≠ ⊤)
    (hC12 : IsC12On (fun X Y => (gesFunctional F t X Y).toReal) O) :
    DifferentiableAt ℝ (timeAverage F t) 0 ∧
    (∀ j k : Fin N,
      kineticCoeff F t j k =
        (1 / 2 : ℝ) * ∫ s in (-t)..t, correlation F j k s * (1 - |s| / t)) ∧
    (∀ j k : Fin N, kineticCoeff F t j k = kineticCoeff F t k j) := by sorry

end EntFluctCDS.GreenKubo
