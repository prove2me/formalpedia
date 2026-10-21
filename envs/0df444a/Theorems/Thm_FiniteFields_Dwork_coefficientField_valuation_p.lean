-- Prove2me | Theorems.Thm_FiniteFields_Dwork_coefficientField_valuation_p
-- name    : FiniteFields.Dwork.coefficientField_valuation_p
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:55:25.278987+00:00
-- url     : https://prove2.me/theorems/796859e2-ba1a-4c2b-90a3-2ab6f8dbb2f6
-- title:
--   Normalization of the valuation on Dwork's unramified coefficient field: $v(p) = e^{-1}$
-- statement:
--   Let $p$ be a prime and let $k$ be a finite field of characteristic $p$. Let $W(k)$ be the ring of $p$-typical Witt vectors of $k$; it is a complete discrete valuation ring with maximal ideal $pW(k)$ and residue field $k$. Let $v$ be the discrete valuation of the fraction field $\operatorname{Frac} W(k)$ attached to the maximal ideal of $W(k)$, written multiplicatively with values in $\{0\} \cup \{e^{m} : m \in \mathbb{Z}\}$, and let
--   $$L = \widehat{\operatorname{Frac} W(k)}$$
--   be the completion of $\operatorname{Frac} W(k)$ for $v$, with the valuation (still denoted $v$) extended to $L$. Thus $L$ is the unramified extension of $\mathbb{Q}_p$ of degree $[k : \mathbb{F}_p]$, the coefficient field of Dwork's construction.
--
--   **Statement.** The image of the integer $p$ in $L$ satisfies
--   $$v(p) = e^{-1},$$
--   that is, in additive notation, $\operatorname{ord}(p) = 1$.
--
--   This fixes the normalization of the valuation on the unramified field $L$ of Dwork's §1: the additive valuation $\operatorname{ord}$ is normalized by $\operatorname{ord} p = 1$, the normalization in which $\operatorname{ord} \lambda = 1/(p-1)$ for $\lambda = \zeta_p - 1$.
--
--   **Formalization Note.** The value group is mathlib's $\mathbb{Z}^{m0}$ (multiplicative integers with a zero adjoined), and $e^{-1}$ is `WithZero.exp (-1)`. The field $L$ is `CoefficientField k p`, the valuation completion of `FractionRing (WittVector p k)`, and $v$ is its canonical valuation `Valued.v`; the norm of $L$ used elsewhere is the one attached to this rank-one valuation.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1 (the unramified field $L$ and the normalization of $\operatorname{ord}$). Auxiliary normalization lemma in the formalization of §1 of Dwork 1960; it has no numbered counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/CyclotomicBaseChange/CoefficientNorm.lean`, declaration `WeilConjectures.Dwork.coefficientField_valuation_p`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula

open Polynomial
open scoped NNReal WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]

theorem FiniteFields.Dwork.coefficientField_valuation_p :
    Valued.v (p : CoefficientField k p) = WithZero.exp (-1 : ℤ) := by sorry
