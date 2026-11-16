-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_Supplement_theorem_5_2
-- name    : ExplicitTensorBarrier694.Explicit.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:43:05.631757+00:00
-- url     : https://prove2.me/theorems/54b2649a-9659-4100-9bee-0b7de83053b1
-- title:
--   Theorem 5.2 — the central Koszul flattening $K_p(S_n)$ is invertible
-- statement:
--   Let $p\ge1$ and $n=2p+1$, and let $S_n\in A\otimes B\otimes C$ be the tensor of Definition 5.1 ($A=\mathbb C^n$, $B^*=\mathbb C[t]_{<n}$, $C=\mathbb C^{p+1}\oplus\mathbb C^p$). Then the central Koszul flattening
--
--   $$K_p(S_n):\Lambda^pA\otimes B^*\longrightarrow\Lambda^{p+1}A\otimes C$$
--
--   of Definition 2.2 is invertible.
--
--   Combined with Proposition 2.3, this gives the equality case $\mathrm{Pot}(K_p)=2n-2+\frac2{n+1}$ of Theorem 1.2. It is a companion result and is not used in the proof of the mission goal. This is a paper-proved result awaiting a formal proof.
--
--   Differences from the source:
--   - encoding: S_n with B* = ℂ[t]_{<n} and C = ℂ^{p+1} ⊕ ℂ^p → oddWitness p : Tensor (2p+1) (2p+1) (2p+1), in the monomial basis of B* and with the first p+1 coordinates of C forming ℂ^{p+1}; reason: the entries are the coordinates of X_i(t^u); invertibility of K_p(S_n) does not depend on the choice of bases of B and C
--   - encoding: K_p(S_n) invertible → KoszulInvertible p (oddWitness p): the published koszul matrix gives a bijective linear map; reason: the published Koszul definition is the matrix of Definition 2.2 in exterior bases; a linear map is invertible iff bijective
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Theorem 5.2, p.15; Definition 5.1 (5.1) p.15; Definition 2.2 p.6 (PDF same); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Supplement_OddWitness
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Koszul

namespace ExplicitTensorBarrier694.Explicit.Supplement

open ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Theorem 5.2, p.15. For n = 2p+1 ≥ 3
and the tensor S_n of Definition 5.1 (`oddWitness p`), the central Koszul flattening
K_p(S_n) : Λ^p A ⊗ B* → Λ^{p+1} A ⊗ C is invertible (a bijective linear map). -/
theorem theorem_5_2 (p : ℕ) (hp : 1 ≤ p) :
    KoszulInvertible p (oddWitness p) := by sorry

end ExplicitTensorBarrier694.Explicit.Supplement
