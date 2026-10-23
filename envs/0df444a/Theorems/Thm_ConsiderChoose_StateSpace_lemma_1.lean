-- Prove2me | Theorems.Thm_ConsiderChoose_StateSpace_lemma_1
-- name    : ConsiderChoose.StateSpace.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:54.718575+00:00
-- url     : https://prove2.me/theorems/37757f76-f681-4d52-9565-f3d037243fb0
-- title:
--   Lemma 1, p. 12 — J(S,T) is the sum of J over the connected components of G[S,T]
-- statement:
--   Consider a consider-then-choose instance with a unique ranking: products $[N]$ numbered in preference order, prices $P_i$, customer types $[K]$ with consideration sets $C_j$ and weights $\lambda_j$. For $S\subseteq[N]$ and $T\subseteq[K]$ let $J(S,T)=\max_{A\subseteq S}\sum_{j\in T}\lambda_j\mathrm{Rev}(j,A)$, and let $(S_u,T_u)_{u\in[r]}$ be the connected components of the bipartite graph $G[S,T]$ (an edge joins product $i$ and type $j$ when $i\in C_j$). Then
--   $$J(S,T)=\sum_{u=1}^{r}J(S_u,T_u).$$
--
--   The lemma says that the subproblem splits into independent subproblems, one per connected component. It is the base case of the dynamic program and is applied again after every stocking decision.
--
--   **Formalization Note.** The sum runs over all components of $G[S,T]$, including isolated products $(\{k\},\emptyset)$ and isolated types $(\emptyset,\{j\})$, as in the paper's partition; each of these contributes $0$. No sign or normalisation condition on $\lambda$ or $P$ is assumed: the identity holds for every instance, so the standing assumption that $\lambda$ is a probability vector is not needed and not carried.
-- source:
--   Aouad, Farias & Levi (2021), Management Science 67(6), accepted manuscript (LBS eprint 1426), p. 12, Lemma 1

import Mathlib
import Definitions.Def_ConsiderChoose_StateSpace_Model

namespace ConsiderChoose.StateSpace

theorem lemma_1 {N K : ℕ} (I : Instance N K) (S : Finset (Fin N)) (T : Finset (Fin K)) :
    J I S T = ∑ p ∈ comps I.C S T, J I p.1 p.2 := by sorry

end ConsiderChoose.StateSpace
