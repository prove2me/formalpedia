-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Randomized_inequality_3
-- name    : DoubleGreedyUSM.Randomized.inequality_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:10:23.319976+00:00
-- url     : https://prove2.me/theorems/1fbb6a27-eac3-425b-b9bb-486fc55d65f6
-- title:
--   Inequality (3) — conditional loss in the positive-gain case
-- statement:
--   Let $f:2^{\mathcal N}\to\mathbb R$ be submodular. Take $X\subseteq Y$, $u\in Y\setminus X$, and any comparison set $O$. Put $P=(O\cup X)\cap Y$, $a=f(X\cup\{u\})-f(X)$, and $b=f(Y\setminus\{u\})-f(Y)$. If $a\ge0$ and $b>0$, then
--
--   $$\frac{a}{a+b}\bigl(f(P)-f(P\cup\{u\})\bigr)+\frac{b}{a+b}\bigl(f(P)-f(P\setminus\{u\})\bigr)\le\frac{ab}{a+b}.$$
--
--   This bounds the one-step expected loss of the comparison set in Case 3 of Lemma III.1.
--
--   **Formalization Note** The statement covers any nested pair $X\subseteq Y$ with $u\in Y\setminus X$, a generalization of the reachable states conditioned on in the paper. The positivity of $b$ ensures the denominator is nonzero.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, proof of Lemma III.1, inequality (3) (PDF p. 6)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

namespace DoubleGreedyUSM.Randomized

/-- Inequality (3), Case 3 of the proof of Lemma III.1 (PDF p. 6). -/
theorem inequality_3 {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (Xs Ys O : Finset X) (u : X) (hsub : Xs ⊆ Ys)
    (huY : u ∈ Ys) (huX : u ∉ Xs)
    (ha : 0 ≤ f (insert u Xs) - f Xs)
    (hb : 0 < f (Ys.erase u) - f Ys) :
    let a := f (insert u Xs) - f Xs
    let b := f (Ys.erase u) - f Ys
    let P := (O ∪ Xs) ∩ Ys
    a / (a + b) * (f P - f (insert u P)) +
      b / (a + b) * (f P - f (P.erase u)) ≤ a * b / (a + b) := by sorry

end DoubleGreedyUSM.Randomized
