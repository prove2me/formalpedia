-- Prove2me | Theorems.Thm_BosonicLearn_traceDist_le_one
-- name    : BosonicLearn.traceDist_le_one
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T03:34:48.755394+00:00
-- url     : https://prove2.me/theorems/e318b45b-606c-41c3-98f4-2e08bdfc1424
-- title:
--   The trace distance of two density operators is at most one: $\tfrac12\|\rho-\sigma\|_1\le1$
-- statement:
--   The trace distance between two density operators never exceeds one.
--
--   Let $I$ be an arbitrary index set and let $\rho$ and $\sigma$ be density operators on $\ell^2(I)$, given by their matrices in the standard basis: each is positive, trace class and of trace one. Write $\|\cdot\|_1$ for the trace norm and $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ for the trace distance. Then
--
--   $$
--   D_{\mathrm{tr}}(\rho,\sigma)\le 1 .
--   $$
--
--   Role. An estimate of an unknown state to trace-distance accuracy $\varepsilon\ge1$ therefore needs no measurement: every fixed state is within distance $1$ of the unknown one. The reduction of Corollary 19 uses this for $\epsilon\ge1$, where the claimed number of copies $O\big(n^2\epsilon^{-2}\min\{n,1+1/\nu\}\big)$ can be smaller than one. The bound is also what makes every success event $\{D_{\mathrm{tr}}(\hat\rho,\rho)\le\varepsilon\}$ certain once $\varepsilon\ge1$.
--
--   **Formalization Note** Density operators are the elements of `State I`, and the trace norm is `traceSize`: the infimum of $\sum_k\|\ell_k\|\,\|r_k\|$ over all nuclear expansions $X_{ij}=\sum_k\ell_k(i)\,\overline{r_k(j)}$ with $\ell_k,r_k\in\ell^2(I)$, a value in $[0,\infty]$ that is $\infty$ when no expansion exists. The statement therefore contains that $\rho-\sigma$ is trace class and that its nuclear expansions have total weight arbitrarily close to at most $2$. The source defines the trace distance but does not state this bound separately.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, footnote 1, p. 3 (definition D_tr(ρ, σ) := ½‖ρ − σ‖₁, with optimal distinguishing probability (1 + ε)/2); used in the reduction of Corollary 19, Eq. (221), p. 64

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open scoped ENNReal

namespace BosonicLearn

/-- **The trace distance of two density operators is at most one.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, footnote 1, p. 3: "We write D_tr(ρ, σ) := ½‖ρ − σ‖₁ = ½‖ρ − σ‖_tr, with both ‖·‖₁ and ‖·‖_tr denoting the
trace norm. … if two objects have ε distinguishability distance, the maximal probability that an observer can
distinguish them correctly is (1 + ε)/2."

For any two density operators `ρ, σ` on `ℓ²(I)`, `½‖ρ − σ‖₁ ≤ 1`.

**Formalization Note.** The source does not state the bound; it is the standard consequence of
`‖ρ − σ‖₁ ≤ ‖ρ‖₁ + ‖σ‖₁ = 2`, and it is implicit in the quoted success probability `(1 + ε)/2 ≤ 1`. Here `‖·‖₁` is
`traceSize`, the infimum of `∑ₖ ‖ℓₖ‖‖rₖ‖` over nuclear expansions, so the content is that a density operator has
nuclear expansions of total weight arbitrarily close to its trace. The index type `I` is arbitrary. -/
theorem traceDist_le_one {I : Type} (ρ σ : State I) :
    traceDist ρ.coefficients σ.coefficients ≤ 1 := by sorry

end BosonicLearn
