-- Prove2me | Theorems.Thm_AMPUniversality_Universal_theorem_3
-- name    : AMPUniversality.Universal.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:39.627647+00:00
-- url     : https://prove2.me/theorems/c361fc8e-0ec6-40e1-994f-844be5bd7c3d
-- title:
--   Theorem 3, p. 8 — for two (C,d)-regular sequences with equal entry variances, (1/N)Σᵢ{E p_{N,i}(xᵢᵗ) − E p_{N,i}(x̃ᵢᵗ)} → 0
-- statement:
--   Let $\{(A(N), \mathcal F_N, x^{0,N})\}_{N\ge1}$ and $\{(\tilde A(N), \mathcal F_N, x^{0,N})\}_{N\ge1}$ be two $(C,d)$-regular polynomial sequences of AMP instances (Definition 4) on the same probability space that differ only in the random matrices $A(N)$ and $\tilde A(N)$: the polynomial nonlinearities $\mathcal F_N$ and the initial condition $x^{0,N}$ are the same. Denote by $\{x^t\}_{t\ge0}$ and $\{\tilde x^t\}_{t\ge0}$ the corresponding AMP orbits (Definition 3). Assume further that
--
--   $$
--   \mathbb E\{A_{ij}^2\} = \mathbb E\{\tilde A_{ij}^2\} \qquad \text{for all } N \text{ and all } i<j .
--   $$
--
--   Let $\{p_{N,i}\}_{N\ge0,\,1\le i\le N}$, $p_{N,i}:\mathbb R^q\to\mathbb R$, be polynomials of degree at most $d$ whose coefficients are bounded in absolute value by a constant $B$, for all $N$ and $i\in[N]$. Then for every $t \ge 0$ all the expectations below are finite and
--
--   $$
--   \lim_{N\to\infty} \frac1N \sum_{i=1}^N \Big\{ \mathbb E\, p_{N,i}(x^t_i) - \mathbb E\, p_{N,i}(\tilde x^t_i) \Big\} \;=\; 0 .
--   $$
--
--   The asymptotic behaviour of approximate message passing with polynomial nonlinearities is therefore insensitive to the distribution of the matrix entries, given their variances. This universality is what transfers state evolution, and through it the polytope phase transition, from Gaussian matrices to general sub-Gaussian matrices.
--
--   **Formalization Note** The two sequences are given by two random matrices $A$, $\tilde A$ together with one shared coefficient process $c$ and one shared initial condition $x^0$ on a common probability space; each triple is required to be $(C,d)$-regular with the readings disclosed in the definition `Regular` (sub-Gaussian for all real $\lambda$, scale factor $C/N$, the initial-condition bound almost surely). Since a $(C,d)$-regular sequence is also $(C, d')$-regular for every $d' \ge d$, the restriction of the test polynomials to degree at most $d$ costs no generality. The finiteness of the expectations is stated as part of the conclusion, so the limit cannot hold through the junk value $0$ of non-integrable Bochner integrals.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 8, Theorem 3, (1.8)

import Mathlib
import Definitions.Def_AMPUniversality_Universal_Poly
import Definitions.Def_AMPUniversality_Universal_Orbit
import Definitions.Def_AMPUniversality_Universal_Regular

namespace AMPUniversality.Universal

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 3 (p. 8): let `(A(N), F_N, x^{0,N})` and `(Ã(N), F_N, x^{0,N})` be two
`(C, d)`-regular polynomial sequences of AMP instances that differ only in the random matrices,
with `E A_ij² = E Ã_ij²` for all `N` and `i < j`. Then for any real polynomials `p_{N,i}` on
`ℝ^q` of degree at most `d` with coefficients bounded by `B`, and every `t`,
`lim_{N→∞} (1/N) ∑_i (E p_{N,i}(x^t_i) − E p_{N,i}(x̃^t_i)) = 0`, where `x^t`, `x̃^t` are the
AMP orbits (1.6). The expectations involved exist. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {C : ℝ} {d q : ℕ}
    (A Atil : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
    (c : (N : ℕ) → Ω → Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ)
    (x0 : (N : ℕ) → Ω → Fin N → Fin q → ℝ)
    (hA : IsRegular P C d q A c x0) (hAtil : IsRegular P C d q Atil c x0)
    (hvar : ∀ N (i j : Fin N), i < j → ∫ ω, A N ω i j ^ 2 ∂P = ∫ ω, Atil N ω i j ^ 2 ∂P)
    (B : ℝ) (p : (N : ℕ) → Fin N → (Fin q → Fin (d + 1)) → ℝ)
    (hp : ∀ N (i : Fin N) m, |p N i m| ≤ B) (t : ℕ) :
    (∀ (N : ℕ) (i : Fin N),
      Integrable (fun ω => polyEval1 (p N i) (ampOrbit (A N ω) (c N ω) (x0 N ω) t i)) P ∧
      Integrable (fun ω => polyEval1 (p N i) (ampOrbit (Atil N ω) (c N ω) (x0 N ω) t i)) P) ∧
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i : Fin N,
        (∫ ω, polyEval1 (p N i) (ampOrbit (A N ω) (c N ω) (x0 N ω) t i) ∂P -
          ∫ ω, polyEval1 (p N i) (ampOrbit (Atil N ω) (c N ω) (x0 N ω) t i) ∂P))
      atTop (𝓝 0) := by sorry

end AMPUniversality.Universal
