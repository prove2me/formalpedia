-- Prove2me | Theorems.Thm_AMPUniversality_Universal_proposition_3_avg
-- name    : AMPUniversality.Universal.proposition_3_avg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:41.449986+00:00
-- url     : https://prove2.me/theorems/439f7417-f18c-4b46-850c-dcade84a3628
-- title:
--   Proposition 3, p. 17 (averaged over coordinates, as used in (4.32)) — AMP orbit xᵗ and message-passing vectors zᵗ have moments within KN^{−1/2}
-- statement:
--   Let $\{(A(N), \mathcal F_N, x^{0,N})\}_{N\ge1}$ be a $(C,d)$-regular polynomial sequence of AMP instances. Denote by $\{x^t\}_{t\ge0}$ the corresponding AMP orbit,
--
--   $$
--   x^{t+1}_i(r) \;=\; \sum_{\ell} A_{\ell i} f^\ell_r(x^t_\ell, t) \;-\; \sum_\ell A_{\ell i}^2 \sum_s f^i_s(x^{t-1}_i, t-1)\, \frac{\partial f^\ell_r}{\partial x(s)}(x^t_\ell, t),
--   $$
--
--   and by $\{z^t\}_{t\ge0}$ the vectors defined by (4.6) while iterating the message-passing recursion (4.5). For a vector $y \in \mathbb R^q$ and an exponent vector $m = (m(1),\dots,m(q)) \in \mathbb N^q$ write $y^m = \prod_{r} y(r)^{m(r)}$. Then for every $t \ge 1$ and every $m \in \mathbb N^q$ there is a constant $K$, independent of $N$, such that for every $N$ all the moments below are finite and
--
--   $$
--   \frac1N \sum_{i=1}^N \big|\,\mathbb E[(x^t_i)^m] - \mathbb E[(z^t_i)^m]\,\big| \;\le\; K N^{-1/2}.
--   $$
--
--   The memory term of AMP is what makes its iterates close to the non-backtracking message-passing iteration; combined with Proposition 1 this transfers universality from $z^t$ to the AMP orbit (Theorem 3), whose conclusion, an average over $i$, needs only this averaged bound in the step (4.32).
--
--   **Formalization Note** The paper states the bound for each coordinate $i$ separately. That version is false under Definition 4: take $q = 1$, $f(\cdot;0) = x$, $f(\cdot;1) = x^2$, deterministic $x^{0,N}$ with $x^{0,N}_1 = \sqrt{C\log(N(C-1)+1)}$ and all other coordinates $0$ (so $\sum_i e^{(x^{0,N}_i)^2/C} = NC$), and $A_{ij} = Y_{ij}/\sqrt N$ with $Y$ centered, bounded and $\mathbb E Y^3 = 2$. Then $x^2_1 - z^2_1 = -(x^{0,N}_1)^2\sum_\ell A_{1\ell}^3$ exactly, whose mean is of order $N^{-1/2}\log N$. The averaged form stated here is what the proof of Theorem 3 needs. Following Note 2 of the paper (p. 16), the constant is chosen before the sequence: it depends only on $C, d, q, t, m$. The memory term is absent at $t = 0$. Integrability of both moments is part of the conclusion.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 17, Proposition 3 (in the averaged form used on p. 29, (4.32))

import Mathlib
import Definitions.Def_AMPUniversality_Universal_Poly
import Definitions.Def_AMPUniversality_Universal_Orbit
import Definitions.Def_AMPUniversality_Universal_Regular

namespace AMPUniversality.Universal

open MeasureTheory ProbabilityTheory

/-- Proposition 3 (p. 17), corrected to the coordinate-averaged form used in (4.32), with Note 2:
for a `(C, d)`-regular polynomial sequence, the moments of the AMP orbit `x^t_i` of (1.6) and of
the message-passing vectors `z^t_i` of (4.5)–(4.6) are finite, and their differences satisfy
`(1/N) ∑_i |E[(x^t_i)^m] − E[(z^t_i)^m]| ≤ K N^{-1/2}`, for every `t ≥ 1` and `m ∈ ℕ^q`.
The constant `K` depends only on `C, d, q, t, m` (Note 2), not on `N` or the sequence.
(The page states the bound for each `i` separately; that version fails when one coordinate of
`x^{0,N}` grows like `√(log N)`, which Definition 4(3) allows.) -/
theorem proposition_3_avg (C : ℝ) (d q t : ℕ) (ht : 1 ≤ t) (m : Fin q → ℕ) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (A : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
      (c : (N : ℕ) → Ω → Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ)
      (x0 : (N : ℕ) → Ω → Fin N → Fin q → ℝ),
      IsRegular P C d q A c x0 →
      ∀ N : ℕ,
        (∀ i : Fin N,
          Integrable (fun ω => monomial (ampOrbit (A N ω) (c N ω) (x0 N ω) t i) m) P ∧
          Integrable (fun ω => monomial (mpOrbit (A N ω) (c N ω) (x0 N ω) t i) m) P) ∧
        (N : ℝ)⁻¹ * ∑ i : Fin N,
            |∫ ω, monomial (ampOrbit (A N ω) (c N ω) (x0 N ω) t i) m ∂P -
              ∫ ω, monomial (mpOrbit (A N ω) (c N ω) (x0 N ω) t i) m ∂P|
          ≤ K * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end AMPUniversality.Universal
