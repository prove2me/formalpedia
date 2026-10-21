-- Prove2me | Theorems.Thm_FiniteFields_Dwork_dworkTraceAdditiveCharacter_ne_zero
-- name    : FiniteFields.Dwork.dworkTraceAdditiveCharacter_ne_zero
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:48:57.039871+00:00
-- url     : https://prove2.me/theorems/c1bec6c9-600e-4157-bf30-9a9b9e72bc5b
-- title:
--   The additive character $x\mapsto\zeta^{\operatorname{Tr}(x)}$ is nontrivial
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$. Let $K$ be the completed fraction field of the Witt vectors $W(k)$, and $L=K(\zeta)$ its $p$-th cyclotomic extension with $\zeta$ a fixed primitive $p$-th root of unity. Define
--   $$\psi\colon k\to L,\qquad \psi(x)=\zeta^{\operatorname{Tr}_{k/\mathbb F_p}(x)},$$
--   where the exponent is the absolute trace of $x$, an element of $\mathbb F_p=\mathbb Z/p\mathbb Z$, represented by an integer in $\{0,\dots,p-1\}$. Then $\psi$ is an additive character of $k$ (that is, $\psi(x+y)=\psi(x)\psi(y)$ and $\psi(0)=1$), and it is nontrivial: there is $x\in k$ with
--   $$\psi(x)\ne1 .$$
--
--   Dwork's character sums require a nontrivial additive character: orthogonality $\sum_{x\in k}\psi(x)=0$ is what converts the count of zeros of a polynomial into a sum of character values, as in §3 (16)–(21).
--
--   **Formalization Note** In Mathlib (`AddChar`) the trivial character $x\mapsto1$ is denoted both `1` and `0`; the statement `dworkTraceAdditiveCharacter k p ≠ 0` therefore means that $\psi$ is nontrivial. The absolute trace is `Algebra.trace (ZMod p) k`.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1, formulas (7)–(8) (the additive character $\Theta$ built from the absolute trace), as used in §3 (16)–(21); auxiliary lemma in the formalization, with no separately numbered counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/AdditiveCharacter.lean`, declaration `WeilConjectures.Dwork.dworkTraceAdditiveCharacter_ne_zero`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

open scoped BigOperators WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq

theorem FiniteFields.Dwork.dworkTraceAdditiveCharacter_ne_zero :
    dworkTraceAdditiveCharacter k p ≠ 0 := by sorry
