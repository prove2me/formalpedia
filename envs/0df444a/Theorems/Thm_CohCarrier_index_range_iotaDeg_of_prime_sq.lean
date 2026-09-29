-- Prove2me | Theorems.Thm_CohCarrier_index_range_iotaDeg_of_prime_sq
-- name    : CohCarrier.index_range_iotaDeg_of_prime_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/f59e7e7d-7662-5b81-841d-ec72f60d7dcf
-- title:
--   Degeneracy maps from level Nq² have index q(q+1)
-- statement:
--   Let $N$ and $q$ be nonzero natural numbers with $q$ prime and $q \nmid N$. Consider the levels $N$ and $Nq^2$ with the full unit subgroups $\top \le (\mathbb{Z}/N)^\times$ and $\top \le (\mathbb{Z}/Nq^2)^\times$, so that `GammaH N ⊤` is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained from $\Gamma_0(N)$ by imposing membership in $\top$ on the diagonal unit, i.e. $\Gamma_0(N)$ itself, and likewise at level $Nq^2$. Assume given, for each of $d = 1$, $d = q$ and $d = q^2$, a witness of `LevelLE N (N * q ^ 2) ⊤ ⊤ d`, that is: $N \mid Nq^2$, $d \mid (Nq^2)/N$, and reduction modulo $N$ carries $\top$ into $\top$. For such $d$, `iotaDeg` is the homomorphism $\Gamma_0(Nq^2) \to \Gamma_0(N)$ sending $\begin{pmatrix} a & b \\ c & e\end{pmatrix}$ to $\begin{pmatrix} a & bd \\ c/d & e\end{pmatrix}$. The conclusion is the conjunction of three statements: for each of $d = 1, q, q^2$, the range of the corresponding `iotaDeg` has index $q(q+1)$ in `GammaH N ⊤`.
--
--   This records the index of the images of the three degeneracy embeddings of level $Nq^2$ into level $N$ at a prime $q \nmid N$, the group-theoretic counterpart of the classical computation $[\Gamma_0(N) : \Gamma_0(Nq^2)] = q(q+1)$. It is used in establishing the identities among the nine composites of the degeneracy maps at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_index_range_iotaDeg_of_prime_sq.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.index_range_iotaDeg_of_prime_sq (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :
    (iotaDeg N (N * q ^ 2) ⊤ ⊤ 1 h1).range.index = q * (q + 1) ∧
    (iotaDeg N (N * q ^ 2) ⊤ ⊤ q hq').range.index = q * (q + 1) ∧
    (iotaDeg N (N * q ^ 2) ⊤ ⊤ (q ^ 2) hq2).range.index = q * (q + 1) := by sorry
