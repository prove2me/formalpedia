-- Prove2me | Theorems.Thm_EthierKurtz_oblique_dense_range_lt_one
-- name    : EthierKurtz.oblique_dense_range_lt_one
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T20:57:11.783255+00:00
-- url     : https://prove2.me/theorems/40913d5a-9f39-4886-9184-5febf88924dd
-- title:
--   Dense range of the oblique diffusion resolvent for Hoelder exponent below one
-- statement:
--   Under the hypotheses of the parent (bounded connected open $\Omega\subset\mathbb R^{n+1}$ with $C^{2,\mu}$ boundary, uniformly elliptic $\mu$-Hoelder $a$, $\mu$-Hoelder $b$, $C^{1,\mu}$ oblique field $c$ with $c\cdot\nu\ge\varepsilon>0$), but with $0<\mu<1$, there is $\lambda_0>0$ such that $\{\lambda_0 f-g:(f,g)\in\overline{\mathrm{graph}}\}$ is dense in $C(\overline\Omega)$: $$\forall h\in C(\overline\Omega),\ \forall\delta>0,\ \exists (f,g)\in\overline{\texttt{obliqueDiffusionGraph}\,\Omega\,\mu\,a\,b\,c},\quad \|\lambda_0 f-g-h\|<\delta.$$
--
--   Role: the case $\mu<1$ of the parent, where the Schauder theory of the oblique derivative problem applies directly.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Theorem 6.31

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_dense_range_lt_one (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ < 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by sorry

end EthierKurtz
