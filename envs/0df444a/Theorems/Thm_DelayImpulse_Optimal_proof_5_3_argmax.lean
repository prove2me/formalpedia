-- Prove2me | Theorems.Thm_DelayImpulse_Optimal_proof_5_3_argmax
-- name    : DelayImpulse.Optimal.proof_5_3_argmax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:33.79927+00:00
-- url     : https://prove2.me/theorems/13999e0b-e064-43f1-93c3-de33181c94de
-- title:
--   Proof of Proposition 5.3, (5.17)–(5.18), p. 8 — a measurable maximiser over a finite set of measurable functions exists
-- statement:
--   Let $(\Omega,\mathcal G)$ be a measurable space, $E$ a measurable space in which singletons are measurable, $U\subset E$ a finite nonempty set, and $X_\beta:\Omega\to\mathbb R$ a $\mathcal G$-measurable function for each $\beta\in U$. Then there is a $\mathcal G$-measurable $b:\Omega\to E$ with values in $U$ such that, for every $\omega$,
--   $$X_{b(\omega)}(\omega)=\max_{\beta\in U}X_\beta(\omega).$$
--
--   This is the construction of p. 8, stated for a general finite family: enumerating $U=\{\beta_1,\dots,\beta_p\}$ and putting $b=\beta_j$ on $\mathcal A_j\setminus\bigcup_{k<j}\mathcal A_k$, where $\mathcal A_i$ is the set on which $\beta_i$ attains the maximum. Applied with $\mathcal G=\mathcal F_{\tau}$ and $X_\beta$ the conditional expectations in (5.17), it produces the $\mathcal F_\tau$-measurable maximisers $\beta^*_n$ of Theorem 6.1.
--
--   **Formalization Note** The maximum is `Finset.sup'`.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, p. 8, proof of Proposition 5.3, (5.17)–(5.18) and the construction of βⁿ₀ via the sets 𝒜ᵢ

import Mathlib

open MeasureTheory

namespace DelayImpulse.Optimal
theorem proof_5_3_argmax {Ω E : Type} [MeasurableSpace E] [MeasurableSingletonClass E]
    (G : MeasurableSpace Ω) (U : Finset E) (hU : U.Nonempty) (X : E → Ω → ℝ)
    (hX : ∀ β ∈ U, Measurable[G] (X β)) :
    ∃ b : Ω → E, Measurable[G] b ∧ (∀ ω, b ω ∈ U) ∧
      ∀ ω, X (b ω) ω = U.sup' hU (fun β => X β ω) := by sorry
end DelayImpulse.Optimal
