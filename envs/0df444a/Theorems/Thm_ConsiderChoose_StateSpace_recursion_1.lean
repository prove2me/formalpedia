-- Prove2me | Theorems.Thm_ConsiderChoose_StateSpace_recursion_1
-- name    : ConsiderChoose.StateSpace.recursion_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:51.378996+00:00
-- url     : https://prove2.me/theorems/f97bf149-3771-4286-bc00-ba9a21f7e235
-- title:
--   §3, Eq. (1), p. 13 — the dynamic-programming recursion: stock min(S) or not
-- statement:
--   In the setting of the consider-then-choose assortment problem with a unique ranking (products $[N]$ numbered in preference order, prices $P_i$, types $[K]$ with consideration sets $C_j$ and weights $\lambda_j$), let $(S,T)$ be a subproblem with $S\neq\emptyset$ whose graph $G[S,T]$ is connected, and let $i=\min(S)$ be its most preferred product. Write $T(i)=\{j\in T: i\in C_j\}$, let $(S^+_u,T^+_u)_{u\in[r(+)]}$ be the connected components of $G[S\setminus\{i\},T\setminus T(i)]$ and $(S^-_u,T^-_u)_{u\in[r(-)]}$ those of $G[S\setminus\{i\},T]$. Then
--   $$J(S,T)=\max\Big[\,P_i\sum_{j\in T(i)}\lambda_j+\sum_{u=1}^{r(+)}J(S^+_u,T^+_u)\ ,\ \sum_{u=1}^{r(-)}J(S^-_u,T^-_u)\Big].$$
--
--   The first term is the value of stocking product $i$: every type in $T(i)$ buys it, and those types leave the problem. The second is the value of not stocking it. This is the recursion the dynamic program solves on its state space.
--
--   **Formalization Note.** The component sums run over all components, trivial ones included (they contribute $0$). No condition on $\lambda$ or $P$ is assumed.
-- source:
--   Aouad, Farias & Levi (2021), Management Science 67(6), accepted manuscript (LBS eprint 1426), pp. 12–13, §3, Eq. (1) (Recursive step, Cases 1–2)

import Mathlib
import Definitions.Def_ConsiderChoose_StateSpace_Model

namespace ConsiderChoose.StateSpace

theorem recursion_1 {N K : ℕ} (I : Instance N K) (S : Finset (Fin N)) (T : Finset (Fin K))
    (h : S.Nonempty) (hc : GConnected I.C S T) :
    J I S T =
      max (I.P (S.min' h) * ∑ j ∈ typesOf I.C T (S.min' h), I.lam j +
            ∑ p ∈ comps I.C (S.erase (S.min' h)) (T \ typesOf I.C T (S.min' h)), J I p.1 p.2)
        (∑ p ∈ comps I.C (S.erase (S.min' h)) T, J I p.1 p.2) := by sorry

end ConsiderChoose.StateSpace
