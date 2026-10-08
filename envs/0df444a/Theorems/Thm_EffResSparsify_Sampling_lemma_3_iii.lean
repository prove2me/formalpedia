-- Prove2me | Theorems.Thm_EffResSparsify_Sampling_lemma_3_iii
-- name    : EffResSparsify.Sampling.lemma_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:52.861981+00:00
-- url     : https://prove2.me/theorems/f6845741-1eff-4b19-98b6-6457395cece6
-- title:
--   Lemma 3 (iii) — eigenvalues of $\Pi$: $1$ with multiplicity $n-1$, $0$ with multiplicity $m-n+1$
-- statement:
--   Let $G=(V,E,w)$ be a connected weighted graph with $n=|V|$ vertices, $m=|E|$ edges and positive edge weights, and let $\Pi=W^{1/2}BL^{+}B^{\mathsf T}W^{1/2}$. Then the eigenvalues of $\Pi$ are $1$ with multiplicity $n-1$ and $0$ with multiplicity $m-n+1$; equivalently, its characteristic polynomial factors as
--   $$\det(XI-\Pi)=(X-1)^{\,n-1}\,X^{\,m-n+1}.$$
--
--   Taking traces gives $\sum_e w_eR_e=\operatorname{tr}\Pi=n-1$, which identifies the sampling probabilities of Sparsify as $p_e=w_eR_e/(n-1)$.
--
--   **Formalization Note** Multiplicities are algebraic (as roots of the characteristic polynomial); for the symmetric matrix $\Pi$ they equal the geometric ones. The exponent $m-n+1$ is written $m+1-n$ in natural-number arithmetic; for a connected graph $m\ge n-1$, so no truncation occurs.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 6, Lemma 3 (iii)

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace EffResSparsify.Sampling

open Matrix Polynomial

/-- Lemma 3 (iii), p. 6: the eigenvalues of `Π` are `1` with multiplicity `n − 1` and `0` with
multiplicity `m − n + 1`, where `n = |V|` and `m = |E|`; stated as the factorisation of the
characteristic polynomial `det(X·I − Π) = (X − 1)^{n−1} X^{m−n+1}`. -/
theorem lemma_3_iii {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) :
    G.projPi.charpoly =
      (X - 1) ^ (Fintype.card V - 1) * X ^ (Fintype.card E + 1 - Fintype.card V) := by sorry

end EffResSparsify.Sampling
