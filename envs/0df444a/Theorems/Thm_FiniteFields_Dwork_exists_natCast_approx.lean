-- Prove2me | Theorems.Thm_FiniteFields_Dwork_exists_natCast_approx
-- name    : FiniteFields.Dwork.exists_natCast_approx
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:54:44.721026+00:00
-- url     : https://prove2.me/theorems/7094638b-aaa1-463e-bf6e-9c22cbff1d1b
-- title:
--   Elements of $W(\mathbb F_p)$ are approximated by integers modulo $p^M$ inside $W(k)$
-- statement:
--   Let $p$ be a prime and $k$ any field of characteristic $p$ (not necessarily finite). Let $W(\mathbb F_p)\cong\mathbb Z_p$ and $W(k)$ be the rings of $p$-typical Witt vectors, and let $\iota\colon W(\mathbb F_p)\to W(k)$ be the ring homomorphism induced by the inclusion $\mathbb F_p\hookrightarrow k$. Then for every $s\in W(\mathbb F_p)$ and every $M\ge0$ there exist a natural number $N$ and an element $c\in W(k)$ such that
--   $$\iota(s)-N=p^{M}c ,$$
--   that is, $\iota(s)\equiv N \pmod{p^MW(k)}$.
--
--   This says that the image of $W(\mathbb F_p)$ in $W(k)$ lies in the $p$-adic closure of the natural numbers. In the proof of Dwork's formula (8) it is used to replace the Witt-vector trace, which lies in $W(\mathbb F_p)$, by an integer congruent to it modulo an arbitrarily high power of $p$.
--
--   **Formalization Note** The Lean statement names the element of $W(\mathbb F_p)$ `σ`; it is renamed $s$ here to avoid confusion with Frobenius. The natural number $N$ is cast into $W(k)$, and the finiteness assumption on $k$ present in the surrounding file is explicitly omitted for this statement.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1, formula (8) (identification of the product of splitting values with $\zeta^{\operatorname{Tr}(x)}$); auxiliary lemma in the formalization of (8), with no direct counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/WittTraceCharacter/TraceLimit.lean`, declaration `WeilConjectures.Dwork.exists_natCast_approx`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra
omit [Finite k]

theorem FiniteFields.Dwork.exists_natCast_approx (σ : CoefficientRing (ZMod p) p) (M : ℕ) :
    ∃ N : ℕ, ∃ c : CoefficientRing k p,
      wittPrimeFieldMap k p σ - (N : CoefficientRing k p)
        = (p : CoefficientRing k p) ^ M * c := by sorry
