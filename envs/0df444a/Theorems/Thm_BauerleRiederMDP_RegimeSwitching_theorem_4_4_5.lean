-- Prove2me | Theorems.Thm_BauerleRiederMDP_RegimeSwitching_theorem_4_4_5
-- name    : BauerleRiederMDP.RegimeSwitching.theorem_4_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:29:26.279422+00:00
-- url     : https://prove2.me/theorems/d4260d48-2aae-4fce-8326-a4fa60a6acc6
-- title:
--   Theorem 4.4.5 — under icv-ordered regimes the value rises and consumption falls with the regime (corrected: $\alpha^*\ge0$ in a))
-- statement:
--   Consider the regime-switching consumption-investment problem of §4.4 with environment states $E_Y=\{1,\dots,m\}$, one stock whose return $R(j)>-1$ has support independent of $j$, interest rate $i\ge0$, discount factor $\beta\in(0,1]$, Assumption (FM) for every $j$, and power utilities $U_c(x)=U_p(x)=\frac1\gamma x^\gamma$, $0<\gamma<1$, $\delta=(1-\gamma)^{-1}$. Let $(Y_n)$ be stochastically monotone and suppose
--
--   $$
--   Q_1\le_{icv}Q_2\le_{icv}\dots\le_{icv}Q_m .
--   $$
--
--   Let $\alpha^*(j)$ be an optimal solution of (4.21), with $\alpha^*(j)\ge0$ for $j\in E_Y$, and let $c_n^*(x,j)=x(\gamma d_n(j))^{-\delta}$ and $a_n^*(x,j)=(x-c_n^*(x,j))\alpha^*(j)$ be the optimal consumption and investment of Theorem 4.4.2. Then:
--
--   1. $J_n(x,j)$ is increasing in $j$ and $c_n^*(x,j)$ is decreasing in $j$;
--   2. if $\alpha^*(j)$ is the unique optimal solution of (4.21) for every $j$, then $a_n^*(x,j)$ is increasing in $j$.
--
--   In a better environment the investor is richer in value, consumes a smaller fraction of wealth and, when long in the stock, invests more.
--
--   Differences from the source:
--   - correction: a) holds without a sign condition; b) assumes α*(j) ≥ 0 for j ∈ E_Y → α*(j) ≥ 0 for all j is a hypothesis of both a) and b); reason: a) is false without it: m = 2, identity chain, i = 0, β = 1, γ = 1/2, R(j) ∈ {−0.5, 0.5} with ℙ(R(1) = 0.5) = 0.1 and ℙ(R(2) = 0.5) = 0.2 (Q_1 ≤_st Q_2, so Q_1 ≤_icv Q_2); both investors sell short and v(1) ≈ 1.281 > v(2) ≈ 1.166, so J_1(x, 1) > J_1(x, 2) and c*_1(x, 1) < c*_1(x, 2) for x > 0; the book's proof of a) uses that y ↦ (1 + α*(j)y)^γ is increasing
--   - reading: α*(j) is the optimal solution of (4.21) (in b)) → in b), every maximizer of (4.21) in Ã equals α*(j); reason: the definite article presupposes uniqueness; if R(j) = 0 a.s. for all j every α is optimal and b) fails for an arbitrary nonnegative choice
--   - encoding: c*_n(x, j) and a*_n(x, j), the optimal consumption and investment → the closed forms x(γ d_n(j))^{−δ} and (x − c*_n(x, j)) α*(j) of Theorem 4.4.2 b), with d_n = dReg; reason: Theorem 4.4.2 b) defines c*_n and a*_n by these formulas
--   - encoding: E_Y = {1, …, m}; Q_j ≤_icv Q_{j+1} → E_Y = Fin m (0-based); IcvLE of the images of Q_j and Q_{j+1} under z ↦ z 0 for consecutive j; reason: index shift only; one stock is the coordinate 0 of a vector in ℝ^1
--   - encoding: the support of R(j) is independent of j → equal supports (Measure.support) of the laws Q_j; reason: the book's standing assumption from p.104, stated for the laws
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.4.5, p.105 (PDF p.119); setting pp.100–104 (PDF pp.114–118)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IcvLE
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsStochMonotone
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_J
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_dReg
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- **Theorem 4.4.5** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.105, PDF p.119), corrected. In the regime-switching model of §4.4
with `E_Y = {1, …, m}`, one stock, the support of `R(j)` independent of `j`, power utilities
`U_c(x) = U_p(x) = x^γ / γ` (`0 < γ < 1`), the standing assumptions of Theorem 4.4.1, a
stochastically monotone environment chain `(Y_n)` and `Q_1 ≤_icv Q_2 ≤_icv … ≤_icv Q_m`, suppose
(correction) that `α*(j) ≥ 0` for `j ∈ E_Y`. Then:
a) `J_n(x, j)` is increasing in `j` and `c*_n(x, j)` is decreasing in `j`;
b) `a*_n(x, j)` is increasing in `j`.

**Formalization Note.** `c*_n(x, j) = x (γ d_n(j))^{-δ}` and `a*_n(x, j) = (x − c*_n(x, j)) α*(j)`
are the optimal consumption and investment of Theorem 4.4.2 b), `d_n = dReg`, and `J_n` is the
value function itself. `α*(j)` is an optimal solution of (4.21) (`hopt`); in b) it is the unique
one (`huniq`, the reading of "the optimal solution": without uniqueness b) fails when
`R(j) = 0` a.s.). The printed theorem asks `α*(j) ≥ 0` in b) only; a) is false without it: with
`m = 2`, the identity chain, `i = 0`, `β = 1`, `γ = 1/2` and `R(j) ∈ {−0.5, 0.5}` with
`ℙ(R(1) = 0.5) = 0.1`, `ℙ(R(2) = 0.5) = 0.2` (so `Q_1 ≤_icv Q_2`), both investors sell short and
`v(1) ≈ 1.281 > v(2) ≈ 1.166`, so `d_1(1) > d_1(2)`: `J_1(x, ·)` decreases and `c*_1(x, ·)`
increases. The chain `Q_1 ≤_icv … ≤_icv Q_m` is stated for consecutive states, as printed. -/
theorem theorem_4_4_5 {m : ℕ} (M : RegimeMarket (Fin m) 1) (i : ℝ) (hi : 0 ≤ i)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hR : ∀ j, ∀ᵐ z ∂(M.Q j : Measure (Fin 1 → ℝ)), ∀ k, -1 < z k)
    (hNA : ∀ j, NoArbitrageLaw (M.Q j : Measure (Fin 1 → ℝ)))
    (hint : ∀ j, Integrable (fun z : Fin 1 → ℝ => ∑ k, |z k|) (M.Q j : Measure (Fin 1 → ℝ)))
    (hsupp : ∀ j k,
      (M.Q j : Measure (Fin 1 → ℝ)).support = (M.Q k : Measure (Fin 1 → ℝ)).support)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmono : IsStochMonotone M.p)
    (hicv : ∀ j : Fin m, ∀ h : j.val + 1 < m,
      IcvLE ((M.Q j : Measure (Fin 1 → ℝ)).map (fun z => z 0))
        ((M.Q ⟨j.val + 1, h⟩ : Measure (Fin 1 → ℝ)).map (fun z => z 0)))
    (αstar : Fin m → Fin 1 → ℝ)
    (hopt : ∀ j, αstar j ∈ admFrac (M.Q j : Measure (Fin 1 → ℝ)) ∧
        ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, αstar j k * z k) ^ γ) ∂(M.Q j : Measure (Fin 1 → ℝ)) =
          powerValue (M.Q j : Measure (Fin 1 → ℝ)) γ)
    (hnn : ∀ j, 0 ≤ αstar j 0) :
    ((∀ n (x : ℝ≥0),
        Monotone (fun j => J M i β (fun c => c ^ γ / γ) (fun c => c ^ γ / γ) n x j)) ∧
      ∀ n (x : ℝ≥0), Antitone (fun j => (x : ℝ) * (γ * dReg M i β γ n j) ^ (-(1 - γ)⁻¹))) ∧
    ((∀ j, ∀ α ∈ admFrac (M.Q j : Measure (Fin 1 → ℝ)),
        ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, α k * z k) ^ γ) ∂(M.Q j : Measure (Fin 1 → ℝ)) =
          powerValue (M.Q j : Measure (Fin 1 → ℝ)) γ → α = αstar j) →
      ∀ n (x : ℝ≥0), Monotone (fun j =>
        ((x : ℝ) - (x : ℝ) * (γ * dReg M i β γ n j) ^ (-(1 - γ)⁻¹)) * αstar j 0)) := by sorry

end BauerleRiederMDP.RegimeSwitching
