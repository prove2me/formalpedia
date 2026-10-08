-- Prove2me | Theorems.Thm_CouplingHMC_Exact_theorem_2_1
-- name    : CouplingHMC.Exact.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:40.08386+00:00
-- url     : https://prove2.me/theorems/bd7ceed0-7647-4e5f-bbf2-37cd41348933
-- title:
--   Theorem 2.1, p. 11, as its proof delivers it — for |x − y| ≥ 2ℛ and LT² ≤ K/L, R′(x,y)² ≤ (1 − ½KT²) r(x,y)² for exact HMC
-- statement:
--   Suppose Assumption 2.1 holds, let $(q_t,p_t)$ be the exact Hamiltonian flow and let $T\ge0$ with $LT^2\le K/L$. For $x,y\in\mathbb R^d$ with $|x-y|\ge2\mathcal R$ the coupling of §2.3 is synchronous, $\eta=\xi$, and for every realization of $\xi$ (and every value of the coupling parameter $\gamma$)
--
--   $$R'(x,y)^2=|q_T(x,\xi)-q_T(y,\xi)|^2\le\Bigl(1-\frac12KT^2\Bigr)r(x,y)^2,\qquad r(x,y)=|x-y|.$$
--
--   Far apart, one step of exact HMC is a strict contraction of the coupling distance, deterministically.
--
--   **Formalization Note.** The paper prints (22) as $R'(x,y)\le(1-\tfrac12KT^2)\,r(x,y)$ and derives it from Lemma 3.4, which bounds the *square*. The printed bound is false: for $U(x)=\tfrac12|x|^2$ (so $\mathcal R=0$, $K=L=1$) the flow gives $R'=|\cos T|\,r$, and $\cos T>1-\tfrac12T^2$ for every $T\in(0,1]$. The statement here is the one the proof delivers, the square form of (55), which implies $R'\le(1-\tfrac14KT^2)r$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, Theorem 2.1, (22), p. 11, with its proof, §5, p. 34

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- Theorem 2.1 (p. 11), in the form its proof (p. 34) delivers from Lemma 3.4: for exact HMC,
`T ≥ 0` with `LT² ≤ K/L` and `|x - y| ≥ 2ℛ`, the (synchronous) coupling satisfies
`R'(x, y)² ≤ (1 - ½KT²) r(x, y)²` for every realization `ω = (ξ, Ũ)` and every `γ`.
(The printed bound (22), `R' ≤ (1 - ½KT²) r`, fails for `U(x) = |x|²/2`.) -/
theorem theorem_2_1 {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (T : ℝ) (hT : 0 ≤ T)
    (hTK : L * T ^ 2 ≤ K / L) (γ : ℝ) (x y : E d) (hxy : 2 * ℛ ≤ ‖x - y‖) (ω : E d × ℝ) :
    Rprime q T γ ℛ x y ω ^ 2 ≤ (1 - 1 / 2 * K * T ^ 2) * ‖x - y‖ ^ 2 := by sorry

end CouplingHMC.Exact
