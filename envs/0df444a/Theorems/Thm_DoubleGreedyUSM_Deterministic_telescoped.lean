-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Deterministic_telescoped
-- name    : DoubleGreedyUSM.Deterministic.telescoped
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:30:39.189317+00:00
-- url     : https://prove2.me/theorems/49a99bd8-b780-41fd-a314-3f2d0191887d
-- title:
--   Proof of Theorem I.1 — the telescoped bound $f(OPT_0) - f(OPT_n) \le f(X_n) + f(Y_n)$
-- statement:
--   Let $\mathcal N$ be a finite ground set, $f : 2^{\mathcal N} \to \mathbb R_{\ge 0}$ a nonnegative submodular function, $OPT$ an optimal solution, and $u_1, \dots, u_n$ an enumeration of $\mathcal N$. Run Algorithm 1 in this order, producing the states $(X_i, Y_i)$ with $X_0 = \emptyset$, $Y_0 = \mathcal N$, and let $OPT_i = (OPT \cup X_i) \cap Y_i$. Then
--   $$f(OPT_0) - f(OPT_n) \le [f(X_n) - f(X_0)] + [f(Y_n) - f(Y_0)] \le f(X_n) + f(Y_n).$$
--
--   This is the sum of Lemma II.2 over $1 \le i \le n$ after telescoping, followed by dropping $f(X_0), f(Y_0) \ge 0$. Together with $OPT_0 = OPT$ and $OPT_n = X_n = Y_n$ it gives $f(X_n) \ge f(OPT)/3$.
--
--   **Formalization Note** Both inequalities are stated. The first uses only submodularity; nonnegativity of $f$ is assumed because the second inequality needs it.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, §II, proof of Theorem I.1, second display (PDF p. 3)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

namespace DoubleGreedyUSM.Deterministic

theorem telescoped {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (O : Finset X)
    (hO : ∀ S, f S ≤ f O) (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    f (optI O (state f l 0)) - f (optI O (state f l l.length)) ≤
        (f (state f l l.length).1 - f (state f l 0).1) +
          (f (state f l l.length).2 - f (state f l 0).2) ∧
      (f (state f l l.length).1 - f (state f l 0).1) +
          (f (state f l l.length).2 - f (state f l 0).2) ≤
        f (state f l l.length).1 + f (state f l l.length).2 := by sorry

end DoubleGreedyUSM.Deterministic
