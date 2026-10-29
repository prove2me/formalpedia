-- Prove2me | Theorems.Thm_EthierKurtz_oblique_base_from_halfspace_model_lt_one
-- name    : EthierKurtz.oblique_base_from_halfspace_model_lt_one
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T21:47:36.08306+00:00
-- url     : https://prove2.me/theorems/39812bf5-548a-4b64-90ee-6f04b12f2d3a
-- title:
--   Base solvability of the oblique derivative problem for $0<\mu<1$
-- statement:
--   Let $\Omega\subset\mathbb{R}^{n+1}$ ($n\ge1$) be a bounded connected open set with $C^{2,\mu}$ boundary, $0<\mu<1$, and let $c$ be a $C^{1,\mu}$ vector field on $\partial\Omega$ with $c\cdot\nu\ge\varepsilon>0$ for the outward normal $\nu$. Then there is $\lambda_0>0$ such that for every bounded $\mu$-Hoelder $h$ on $\overline\Omega$ the problem $$\lambda_0u-\tfrac12\Delta u=h\text{ in }\Omega,\qquad c\cdot\nabla u=0\text{ on }\partial\Omega$$ has a solution in `obliqueDiffusionGraph`.
--
--   Role: the case $\mu<1$ of the parent; it holds without the half-space model hypothesis.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7, Theorem 6.31 (existence for the oblique derivative problem), with Lemma 6.29 and Theorem 6.30; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_base_from_halfspace_model_lt_one :
    ∀ (n : ℕ) (hd : 2 ≤ n + 1)
        (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
        (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
        (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) (hμ1 : μ < 1)
        (hboundary : EthierKurtz.BoundaryCTwiceHolder Ω μ)
        (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
        (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (normal x))
        (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
          ε ≤ ∑ i, c x i * normal x i),
        ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
          HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
            ∃ fg ∈ EthierKurtz.obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
              lam₀ • fg.1 - fg.2 = h := by sorry

end EthierKurtz
