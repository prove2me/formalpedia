-- Prove2me | Theorems.Thm_Diaz_exp_ratMul_isAlgebraic
-- name    : Diaz.exp_ratMul_isAlgebraic
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:39.8824+00:00
-- url     : https://prove2.me/theorems/177f92bd-ce70-4233-a916-026728a38ece
-- title:
--   Rational multiples of a logarithm are logarithms
-- statement:
--   If $e^{u}$ is algebraic and $a \in \mathbb{Q}$, then $e^{au}$ is algebraic. Equivalently, the set $\mathcal{L} = \{u : e^{u} \in \bar{\mathbb{Q}}^{\times}\}$ is stable under multiplication by rationals.
--
--   **Where this sits.** This is the $\mathbb{Q}$-vector-space property of $\mathcal{L}$, used silently throughout Carlo Perassi's work and in particular in the second half of the proof of his algebraic-distance and plane rigidity theorem, where the point $au$ is asserted to lie in the candidate locus $\mathcal{D}$ alongside $u$ so that the algebraic-distance criterion can be applied to the pair $(au, w)$. Together with $|au| = |a||u|$ it is the statement, recorded in his definition of the candidate locus, that $\mathcal{D}$ is stable under $\mathbb{Q}^{\times}$.
--
--   **Proof.** Write $a = p/q$ in lowest terms with $q > 0$. Then $q \cdot (au) = p \cdot u$, so
--
--   $$\bigl(e^{au}\bigr)^{q} = e^{q a u} = e^{pu} = \bigl(e^{u}\bigr)^{p},$$
--
--   which is algebraic (a non-zero algebraic number has algebraic integer and negative powers). An element whose $q$-th power is algebraic is algebraic.
--
--   Entirely standard; recorded because the plane argument of that theorem depends on it.
--
--   **Source.** Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), proof of Proposition 3.8, where it is stated with this argument. The fact is standard; this node only records it in Lean, and claims no novelty of its own.
-- source:
--   Stated with this argument in the proof of Proposition 3.8 of Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.10, 27 September 2026 (GitHub release note-v1.10); the fact is standard. Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.exp_ratMul_isAlgebraic {u : ℂ} (hexp : IsAlgebraic ℚ (Complex.exp u)) (a : ℚ) :
    IsAlgebraic ℚ (Complex.exp ((a : ℂ) * u)) := by sorry
