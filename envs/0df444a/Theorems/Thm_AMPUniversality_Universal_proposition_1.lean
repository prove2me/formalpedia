-- Prove2me | Theorems.Thm_AMPUniversality_Universal_proposition_1
-- name    : AMPUniversality.Universal.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:42.716324+00:00
-- url     : https://prove2.me/theorems/170f3af8-0f4e-490c-ae69-3d51582a3eab
-- title:
--   Proposition 1, p. 16 — moments of the message-passing vectors zᵗᵢ are universal up to KN^{−1/2}
-- statement:
--   Let $\{(A(N), \mathcal F_N, x^{0,N})\}_{N\ge1}$ and $\{(\tilde A(N), \mathcal F_N, x^{0,N})\}_{N\ge1}$ be two $(C,d)$-regular polynomial sequences of AMP instances on the same probability space that differ only in the random matrices: they share the polynomials $\mathcal F_N$ and the initial condition $x^{0,N}$. Assume that $\mathbb E\{A_{ij}^2\} = \mathbb E\{\tilde A_{ij}^2\}$ for all $N$ and all $i<j$. Let $z^t_i$ (resp. $\tilde z^t_i$) be the vectors defined by (4.6) while iterating the message-passing recursion (4.5) with the matrix $A$ (resp. $\tilde A$).
--
--   Then for every $t \ge 1$ and every exponent vector $m = (m(1),\dots,m(q)) \in \mathbb N^q$ there is a constant $K$, independent of $N$, such that for every $N$ and every $i\in[N]$ the moments below are finite and
--
--   $$
--   \big|\,\mathbb E[(z^t_i)^m] - \mathbb E[(\tilde z^t_i)^m]\,\big| \;\le\; K N^{-1/2}.
--   $$
--
--   Here $x^m = \prod_r x(r)^{m(r)}$. Together with Proposition 3 (which compares the AMP orbit with $z^t$ for a single ensemble), this gives Theorem 3.
--
--   **Formalization Note** Following Note 2 of the paper (p. 16: "$K$ is always understood as a function of $d, t, q, m, C$ … independent of $N$"), the constant is chosen before the sequences: it depends only on $C, d, q, t, m$, and the bound holds for every pair of sequences satisfying the hypotheses, every $N$ and every $i$. The integrability of both moments is stated as part of the conclusion, so the bound cannot hold through the junk value $0$ of a non-integrable Bochner integral.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 16, Proposition 1, (4.7)

import Mathlib
import Definitions.Def_AMPUniversality_Universal_Poly
import Definitions.Def_AMPUniversality_Universal_Orbit
import Definitions.Def_AMPUniversality_Universal_Regular

namespace AMPUniversality.Universal

open MeasureTheory ProbabilityTheory

/-- Proposition 1 (p. 16) with Note 2: for two `(C, d)`-regular polynomial sequences that share
the polynomials `F_N` (coefficients `c`) and the initial condition `x^{0,N}` and whose matrix
entries have equal second moments, the moments of the message-passing vectors `z^t_i` of
(4.5)–(4.6) agree up to `K N^{-1/2}`, for every `t ≥ 1` and `m ∈ ℕ^q`. The constant `K` depends
only on `C, d, q, t, m` (Note 2), not on `N`, `i` or the sequences. -/
theorem proposition_1 (C : ℝ) (d q t : ℕ) (ht : 1 ≤ t) (m : Fin q → ℕ) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (A Atil : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
      (c : (N : ℕ) → Ω → Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ)
      (x0 : (N : ℕ) → Ω → Fin N → Fin q → ℝ),
      IsRegular P C d q A c x0 → IsRegular P C d q Atil c x0 →
      (∀ N (i j : Fin N), i < j → ∫ ω, A N ω i j ^ 2 ∂P = ∫ ω, Atil N ω i j ^ 2 ∂P) →
      ∀ (N : ℕ) (i : Fin N),
        Integrable (fun ω => monomial (mpOrbit (A N ω) (c N ω) (x0 N ω) t i) m) P ∧
        Integrable (fun ω => monomial (mpOrbit (Atil N ω) (c N ω) (x0 N ω) t i) m) P ∧
        |∫ ω, monomial (mpOrbit (A N ω) (c N ω) (x0 N ω) t i) m ∂P -
            ∫ ω, monomial (mpOrbit (Atil N ω) (c N ω) (x0 N ω) t i) m ∂P|
          ≤ K * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end AMPUniversality.Universal
