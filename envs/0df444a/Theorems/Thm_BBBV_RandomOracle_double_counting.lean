-- Prove2me | Theorems.Thm_BBBV_RandomOracle_double_counting
-- name    : BBBV.RandomOracle.double_counting
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:54.070557+00:00
-- url     : https://prove2.me/theorems/40f17283-0e57-4d98-8c65-d9b1b0e2c4a3
-- title:
--   Proof of Theorem 3.5, p. 9 — the oracles of ℬ on which M fails are at least half the oracles of 𝒜 on which M succeeds
-- statement:
--   Let $n \ge 1$ and let $\mathrm{Good}$ be any property of oracles $A : \{0,1\}^n \to \{0,1\}^n$ (in the application: "$M$ correctly decides whether $1^n \in \mathcal{L}_A$"). For an oracle $A$ and $y \in \{0,1\}^n$ write $A_y$ for $A$ with its answer at $y$ changed to $1^n$. Suppose that for every $A \in \mathcal{A}$ (no preimage of $1^n$) with $\mathrm{Good}(A)$, at least $2^{n-1}$ strings $y$ have $\neg\mathrm{Good}(A_y)$. Then
--   $$\#\{A \in \mathcal{A} : \mathrm{Good}(A)\} \le 2\,\#\{B \in \mathcal{B} : \neg\mathrm{Good}(B)\},$$
--   where $\mathcal{B}$ is the set of oracles under which $1^n$ has exactly one preimage.
--
--   This is the counting step of the proof of Theorem 3.5: each successful oracle of $\mathcal{A}$ maps to at least $2^{n-1}$ failing oracles of $\mathcal{B}$, and each oracle of $\mathcal{B}$ is the image of at most $2^n - 1$ oracles of $\mathcal{A}$.
--
--   **Formalization Note** The statement is for an arbitrary property $\mathrm{Good}$, which is all the counting uses; the hypothesis is the conclusion of the preceding step of the proof (Corollary 3.4 with $\varepsilon = 1/13$ and the $1/13$ step).
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 9, proof of Theorem 3.5, sixth paragraph

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

open Classical in
theorem double_counting {n : ℕ} (hn : 1 ≤ n) (Good : (Str n → Str n) → Prop)
    (h : ∀ A, NoInverse A → Good A →
      2 ^ (n - 1) ≤ (Finset.univ.filter fun y => ¬ Good (Function.update A y (ones n))).card) :
    (Finset.univ.filter fun A => NoInverse A ∧ Good A).card ≤
      2 * (Finset.univ.filter fun B => UniqueInverse B ∧ ¬ Good B).card := by sorry

end BBBV.RandomOracle
