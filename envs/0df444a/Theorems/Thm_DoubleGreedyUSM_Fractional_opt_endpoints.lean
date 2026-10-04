-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Fractional_opt_endpoints
-- name    : DoubleGreedyUSM.Fractional.opt_endpoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:05:23.914727+00:00
-- url     : https://prove2.me/theorems/a7c08d19-be38-48fa-9f78-67643073d115
-- title:
--   Appendix A — $OPT_0 = OPT$ and $OPT_n = x_n = y_n$ along Algorithm 4
-- statement:
--   Let $f : 2^{\mathcal N} \to \mathbb R$ be submodular with multilinear extension $F$, let $OPT \subseteq \mathcal N$ be an optimal solution ($f(S) \le f(OPT)$ for all $S$), and run Algorithm 4 on $f$ in an order $u_1, \dots, u_n$ of the ground set. With $OPT_i = (OPT \vee x_i) \wedge y_i$:
--
--   1. $OPT_0 = OPT$ (as a characteristic vector), and its multilinear value is the value of the optimal solution, $F(OPT) = f(OPT)$;
--   2. $OPT_n = x_n = y_n$.
--
--   $$OPT_0 = \mathbf 1_{OPT}, \quad F(\mathbf 1_{OPT}) = f(OPT), \qquad OPT_n = x_n = y_n .$$
--
--   So the sequence $F(OPT_0), \dots, F(OPT_n)$ starts at the optimal value and ends at $F(x_n)$, the expected value of the algorithm's output $R(x_n)$; the analysis bounds the total decrease along this sequence.
--
--   **Formalization Note.** The order is a duplicate-free list containing every element of the finite type $X$. The optimality hypothesis on $OPT$ is kept as on the page, although the identities hold for every set.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Appendix A, paragraph after Theorem A.1 (PDF p. 9)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- App. A, after Theorem A.1 (PDF p. 9): with `OPT_i = (OPT ∨ x_i) ∧ y_i` along a run of
Algorithm 4 in the order `l` of the ground set, `OPT_0 = OPT` (as a characteristic vector, whose
multilinear value is `f(OPT)`), and `OPT_n = x_n = y_n`. -/
theorem opt_endpoints {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    optI O (state f l 0) = indicator O ∧
    NonmonotoneSubmod.Shared.F f (indicator O) = f O ∧
    optI O (state f l l.length) = (state f l l.length).1 ∧
    (state f l l.length).1 = (state f l l.length).2 := by sorry

end DoubleGreedyUSM.Fractional
