-- Prove2me | Theorems.Thm_BlockSSM_lemma_7
-- name    : BlockSSM.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:39.3642+00:00
-- url     : https://prove2.me/theorems/84fd55c4-9d8c-4e95-8670-e763d0811a20
-- title:
--   Lemma 7: linearization without larger blocks
-- statement:
--   Let $H$ be a finite group acting faithfully by bijections on an affine subspace $W\subseteq\mathbb C^n=\prod_i\mathbb C^{n_i}$, with $n_i\le b$ for all $i$. Suppose that the action of each $h\in H$ on $W$ is the restriction of an affine map with the prescribed block-diagonal linear part: there are matrices $A^{(i)}\in\mathbb C^{n_i\times n_i}$ and a vector $c$ with
--   $$
--   (h\cdot x)_i=A^{(i)}x_i+c_i\qquad(x\in W,\ i=1,\dots,m).
--   $$
--   Then $H$ has a faithful complex representation of dimension at most $n=\sum_i n_i$, all of whose irreducible constituents have degree at most $b$.
--
--   The point of the lemma is that passing to a linear representation does not enlarge any block.
--
--   **Formalization Note** The matrices may depend on $h$, need not be unique and may be singular off $W$. The empty subspace is allowed; faithfulness then forces $H$ to be trivial.
--
--   Differences from the source:
--   - generalization: an integer block bound $b\ge 1$ → an arbitrary $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`); reason: every integer $b\ge 1$ is a case through the cast; the lemma does not use $b\ge 1$
--   - encoding: $H$ acts by affine bijections on $V_E$ → a faithful homomorphism into the bijections of $W$, each given by an affine formula on $W$; reason: affineness on $W$ follows from the extension hypothesis, so it need not be stated separately
--   - encoding: hidden state space $\mathbb C^n$ with block-diagonal $A_g$ → the product $\prod_i\mathbb C^{n_i}$ with one matrix per block; reason: the same space split along the partition; the linear part is block-diagonal by construction
--   - encoding: a faithful complex representation of $H$ of dimension at most $n$ → an injective `Representation ℂ H (Fin d → ℂ)` with $d\le\sum_i n_i$; reason: every $d$-dimensional complex representation is isomorphic to one on $\mathbb C^d$, and faithful means injective
--   - encoding: all irreducible constituents of degree at most $b$ → every irreducible subrepresentation has dimension at most $b$; reason: by Maschke every irreducible constituent is isomorphic to an irreducible subrepresentation
--   - generalization: the affine subspace $V_E=E(V)$, which is nonempty → any `AffineSubspace` $W$ of $\mathbb C^n$, the empty one included; reason: on the empty $W$ faithfulness forces $H$ trivial and $d=0$ works; every nonempty $W$, in particular the source's $V_E$, is a case
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 7, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_Tracker
import Definitions.Def_BlockSSM_IrrepDegreesLE

namespace BlockSSM

/-- **Lemma 7 (Linearization without larger blocks).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 7, p.3 (PDF p.4): "Suppose a finite
group H acts faithfully by affine bijections on an affine subspace V_E ⊆ ℂⁿ. Suppose each action
extends to an affine map with the prescribed block-diagonal linear part. Then H has a faithful
representation of dimension at most n, all of whose irreducible constituents have degree at most b."

**Formalization Note.** The action is a faithful homomorphism `α` into the bijections of `W`.
Affineness of each bijection follows from `hext`. The extending matrices may depend on `h`, need not
be unique and may be singular off `W`. `W` may be empty; faithfulness then forces `H` trivial, and
`d = 0` works. -/
theorem lemma_7 {H : Type*} [Group H] [Finite H] {m : ℕ} (n : Fin m → ℕ) (b : ℕ∞)
    (hn : ∀ i, (n i : ℕ∞) ≤ b) (W : AffineSubspace ℂ (State n))
    (α : H →* Equiv.Perm W) (hα : Function.Injective α)
    (hext : ∀ h : H, ∃ (A : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (c : State n),
      ∀ x : W, ((α h x : W) : State n) = fun i => (A i).mulVec ((x : State n) i) + c i) :
    ∃ d : ℕ, d ≤ ∑ i, n i ∧ ∃ ρ : Representation ℂ H (Fin d → ℂ),
      Function.Injective ρ ∧ IrrepDegreesLE ρ b := by sorry

end BlockSSM
