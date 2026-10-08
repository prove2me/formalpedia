-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Fractional_multilinear_usm_half
-- name    : DoubleGreedyUSM.Fractional.multilinear_usm_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:05:48.050985+00:00
-- url     : https://prove2.me/theorems/34686905-3dca-4050-bd46-2d5e83ad2f20
-- title:
--   Theorem A.1 — Algorithm 4 (MultilinearUSM) is a $(1/2)$-approximation for USM given oracle access to $F$
-- statement:
--   Let $\mathcal N$ be a finite ground set and $f : 2^{\mathcal N} \to \mathbb R_{\ge 0}$ a nonnegative submodular function, i.e. $f(A) + f(B) \ge f(A \cup B) + f(A \cap B)$ for all $A, B \subseteq \mathcal N$. Let $F$ be its multilinear extension, $F(x) = \mathbb E[f(R(x))]$, where $R(x)$ contains each element $u$ independently with probability $x_u$, and let $f(OPT) = \max_{S \subseteq \mathcal N} f(S)$.
--
--   Run Algorithm 4 (MultilinearUSM) on $f$, with oracle access to $F$, in an arbitrary order $u_1, \dots, u_n$ of $\mathcal N$. Then the final vectors coincide, $x_n = y_n$, and the output $R(x_n)$ has expected value at least half the optimum:
--   $$x_n = y_n \qquad\text{and}\qquad f(OPT) \le 2\, F(x_n) = 2\, \mathbb E\bigl[f(R(x_n))\bigr].$$
--
--   This is the fractional counterpart of the randomized double greedy: the algorithm makes all its choices deterministically on the multilinear extension and randomizes only when it rounds $x_n$ to a set, and the ratio $1/2$ is optimal for unconstrained submodular maximization in the value oracle model.
--
--   **Formalization Note.** Only the first sentence of Theorem A.1 (oracle access to $F$) is formalized; the sampling clause, with ratio $(1/2) - o(1)$, is not. "Linear time" is not part of the statement; the bound is for the paper's algorithm, defined line by line, for every order of the ground set. "NSM" in the printed theorem is read as USM. The ratio is multiplied out ($f(OPT) \le 2F(x_n)$), so the statement is meaningful when $f(OPT) = 0$. $F$ is the published `NonmonotoneSubmod.Shared.F`, the sum $\sum_S f(S) \prod_{u \in S} x_u \prod_{u \notin S}(1 - x_u)$, which is the expectation of $f(R(x))$ for $x \in [0,1]^{\mathcal N}$.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Theorem A.1, first sentence (PDF p. 9); conclusion of its proof (PDF p. 9)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Theorem A.1, oracle-access clause (PDF p. 9): Algorithm 4 (MultilinearUSM), run on a
nonnegative submodular `f` in any order `l = [u_1, …, u_n]` of the ground set, ends with
`x_n = y_n`, and its output, the random set `R(x_n)`, has expected value
`F(x_n) ≥ f(OPT)/2`, i.e. `f(OPT) ≤ 2 · F(x_n)`. -/
theorem multilinear_usm_half {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    (state f l l.length).1 = (state f l l.length).2 ∧
    NonmonotoneSubmod.Shared.OPT f
      ≤ 2 * NonmonotoneSubmod.Shared.F f (state f l l.length).1 := by sorry

end DoubleGreedyUSM.Fractional
