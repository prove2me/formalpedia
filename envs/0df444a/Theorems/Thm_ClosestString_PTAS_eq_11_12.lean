-- Prove2me | Theorems.Thm_ClosestString_PTAS_eq_11_12
-- name    : ClosestString.PTAS.eq_11_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:18:21.568861+00:00
-- url     : https://prove2.me/theorems/f5ad1200-3d6c-4458-a979-3df8b15b2a34
-- title:
--   (11)–(12) — the sampled estimate ρ d^R + d^Q falls ε|P| below d with probability ≤ (nm)^{−2} and ε|P| above with probability ≤ (nm)^{−4/3}
-- statement:
--   Let $u,v$ be strings of length $L$, $P$ a nonempty set of positions and $Q$ its complement. Let $R$ be a multiset of $k$ positions drawn independently and uniformly from $P$ (with replacement), $\rho=|P|/k$, and $d^R(u,v)$ the number of entries of $R$ (with multiplicity) at which $u$ and $v$ differ. Let $\varepsilon>0$ and $N\ge1$ with $k\ge(4/\varepsilon^2)\ln N$. Then
--
--   $$\Pr\big(\rho\,d^R(u,v)+d^Q(u,v)\le d(u,v)-\varepsilon|P|\big)\le \exp\!\big(-\tfrac12\varepsilon^2 k\big)\ \text{and}\ \le N^{-2},\qquad \Pr\big(\rho\,d^R(u,v)+d^Q(u,v)\ge d(u,v)+\varepsilon|P|\big)\le N^{-4/3}.$$
--
--   In the paper $N=nm$, $k=|R|=\lceil(4/\varepsilon^2)\log(nm)\rceil$, $u=s^*$ and $v=t'$ or $t_i$; these are the inequalities (11) and (12) of the proof of Fact 2. They say that the sampled distance, rescaled by $\rho$, is a good estimate of the distance on $P$.
--
--   Differences from the source:
--
--   - generalization: N = nm, |R| = ⌈(4/ε²) log(nm)⌉, u = s∗, v = t′ or t_i → any real N ≥ 1, any k ≥ (4/ε²) ln N (including k = 0), any strings u, v; reason: the proof uses only |R| ≥ (4/ε²) ln(nm); the paper's choice is the case N = nm
--   - reading: log(nm) → Real.log, the natural logarithm; reason: (11) needs exp(−ε²|R|/2) ≤ (nm)^{−2}, i.e. |R| ≥ (4/ε²) ln(nm), which is exactly the printed computation with ln
--   - encoding: R a multiset of uniformly random positions of P, ρ = |P|/|R| → R : Fin k → Fin L with law Measure.pi of k uniform laws on P; ρ = (|P| : ℝ)/k; reason: the paper's sampling with replacement; same law
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 11, eqs. (11)–(12) (proof of Fact 2)

import Mathlib
import Definitions.Def_ClosestString_PTAS_Basic

namespace ClosestString.PTAS

open MeasureTheory

/-- **(11)–(12)** (proof of Fact 2, Li, Ma & Wang, arXiv:cs/0002012v1, p. 11): for strings `u, v`
of length `L`, a nonempty position set `P` with complement `Q`, a multiset `R` of `k` independent
uniform positions of `P`, `ρ = |P|/k`, `ε > 0` and `N ≥ 1` with `k ≥ (4/ε²) ln N`:
`Pr(ρ d^R(u,v) + d^Q(u,v) ≤ d(u,v) − ε|P|) ≤ exp(−ε²k/2)` and `≤ N^{−2}`, and
`Pr(ρ d^R(u,v) + d^Q(u,v) ≥ d(u,v) + ε|P|) ≤ N^{−4/3}`. -/
theorem eq_11_12 {A : Type*} [DecidableEq A] {L : ℕ} (u v : Fin L → A) (P : Finset (Fin L))
    (hP : P.Nonempty) (k : ℕ) (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N)
    (hk : 4 / ε ^ 2 * Real.log N ≤ k) :
    Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
        {R | (P.card / k : ℝ) * distSample R u v + distOn Pᶜ u v
              ≤ (hammingDist u v : ℝ) - ε * P.card}
        ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * ε ^ 2 * k)) ∧
      Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
        {R | (P.card / k : ℝ) * distSample R u v + distOn Pᶜ u v
              ≤ (hammingDist u v : ℝ) - ε * P.card}
        ≤ ENNReal.ofReal (N ^ (-(2 : ℝ))) ∧
      Measure.pi (fun _ : Fin k => (PMF.uniformOfFinset P hP).toMeasure)
        {R | (hammingDist u v : ℝ) + ε * P.card
              ≤ (P.card / k : ℝ) * distSample R u v + distOn Pᶜ u v}
        ≤ ENNReal.ofReal (N ^ (-(4 / 3 : ℝ))) := by sorry

end ClosestString.PTAS
