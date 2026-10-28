-- Prove2me | Theorems.Thm_EthierKurtz_componentHolder_extends_closure
-- name    : EthierKurtz.componentHolder_extends_closure
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:14:05.958418+00:00
-- url     : https://prove2.me/theorems/8c349382-7fa4-4d0c-bc90-f7b9b09d99a9
-- title:
--   Component-Hoelder functions extend continuously to the closure of a C^1 domain
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^{n+1}$ be a bounded open set such that every frontier point $x$ has an outward unit normal given by a local $C^1$ defining function $r$ ($\Omega = \{r<0\}$ near $x$, $\nabla r(x)$ a positive multiple of the normal). Let $\varphi$ be continuous on $\Omega$ with finite component oscillation seminorm (1.13): for some $\rho_0, M$,
--   $$|\varphi(y)-\varphi(w)| \le M\rho^{\mu}$$
--   whenever $y, w$ lie in one connected component of $\Omega \cap B(x,\rho)$, $\rho \le \rho_0$, where $\mu > 0$. Then $\varphi$ extends to a bounded continuous function on $\bar\Omega$.
--
--   Role: in the parent, the drift and diffusion coefficients are only assumed component-Hoelder on $\Omega$; this child shows they extend continuously to $\bar\Omega$, so that $Lf$ is a genuine element of $C(\bar\Omega)$ for smooth $f$, which the density argument for the oblique domain needs.
--
--   **Formalization Note**: the extension is stated as a bounded continuous function on the subtype `closure Ω` agreeing with $\varphi$ on $\Omega$.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658. Chapter 8, Section 1, seminorm (1.13); standard fact, cf. D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, Section 4.1 (Hoelder continuous functions extend uniquely to the closure)

import Mathlib
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_ComponentHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem componentHolder_extends_closure (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ)
    (normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hφ : ComponentHolder Ω μ φ) :
    ∃ ψ : (closure Ω) →ᵇ ℝ, ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ Ω →
      ψ x = φ x := by sorry

end EthierKurtz
