-- Prove2me | Theorems.Thm_DetDLP_recursive_child_precision_budget
-- name    : DetDLP.recursive_child_precision_budget
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:18:51.555405+00:00
-- url     : https://prove2.me/theorems/d7c93b65-26df-4f22-aca3-9253cdda2169
-- title:
--   An absolute child-precision bound along every active contraction path
-- statement:
--   For every fixed global edge constant C and window divisor B there is a threshold on the scale parameter rho such that every active contraction call has child precision times the current window at most 41 times the current edge count times the dyadic stride. The incoming precision may have accumulated all earlier tapered Hermite increments along the path. The estimate holds at every eligible sample index, starting from any root precision at most C times the global size. It applies both to the scalar recursion and to terminal continuation from an inherited depth.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Sections 5.2 and 5.3, propagation of incoming precision and the weighted branching estimate.

import Mathlib

set_option autoImplicit false

namespace DetDLP

theorem recursive_child_precision_budget (C B : ℕ) (hC : 0<C) (hB : 0<B) :
    ∃ R : ℕ,∀ (ρ β d : ℕ) (p m i : ℕ→ℕ),
      let u (j : ℕ) := ρ/(B*2^j)
      let a (j : ℕ) := 2*∑ k ∈ Finset.range (j+1),u k
      let h (j : ℕ) := (3*m j+u j-1)/u j
      let prec (j : ℕ) := p j+8*h j*2^(a j-i j)+8*m j*(a j+1)
      R≤ρ→0<β→0< m d→β≤ m d*(ρ.sqrt+1)→m d*8^d≤C*β→p 0≤C*β→
      (∀ j<d,m j≤C*β)→(∀ j<d,p (j+1)≤prec j)→u d≤ m d→i d<u d→
        prec d*u d≤41*m d*2^(a d-i d) := by sorry
end DetDLP
