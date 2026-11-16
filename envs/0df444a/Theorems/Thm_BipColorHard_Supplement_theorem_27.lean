-- Prove2me | Theorems.Thm_BipColorHard_Supplement_theorem_27
-- name    : BipColorHard.Supplement.theorem_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:45:16.689623+00:00
-- url     : https://prove2.me/theorems/c01e7eec-8a49-4b89-9f5d-63d2daa99072
-- title:
--   Theorem 27 — the global maximizers of $\Psi$ are exactly the $2\binom{q}{k}$ pairs $(\alpha^S,\beta^S)$, $(\beta^S,\alpha^S)$
-- statement:
--   Let $q=2k+1$ be odd and let $D=q+1$ if $q\ge5$, and $D=5$ if $q=3$ ($k=1$). For probability vectors $\alpha,\beta$ on $[q]$ let $\Xi(\alpha,\beta)$ be the set of nonnegative $q\times q$ matrices with zero diagonal, row sums $\alpha$ and column sums $\beta$; the pair is feasible when $\Xi(\alpha,\beta)\ne\emptyset$, and then
--   $$\Psi(\alpha,\beta)=\max_{\xi\in\Xi(\alpha,\beta)}\big(D\,H(\xi)-(D-1)H(\alpha)-(D-1)H(\beta)\big),$$
--   with $H$ the Shannon entropy.
--
--   There are constants $\delta,\hat\delta>0$, depending only on $q$, such that the global maximizers of $\Psi$ over the feasible pairs are precisely the $2\binom{q}{k}$ pairs
--   $$(\alpha^S,\beta^S)\quad\text{and}\quad(\beta^S,\alpha^S),\qquad S\subseteq[q],\ |S|=k,$$
--   where
--   $$\alpha^S_i=\begin{cases}\frac1q+\delta,& i\in S,\\ \frac1q-\frac{k}{k+1}\delta,& i\notin S,\end{cases}\qquad \beta^S_i=\begin{cases}\frac1q-\frac{k+1}{k}\hat\delta,& i\in S,\\ \frac1q+\hat\delta,& i\notin S,\end{cases}$$
--   and all these vectors are positive probability vectors. In particular the $2\binom qk$ listed pairs are pairwise distinct.
--
--   The theorem describes the color frequencies among the degree-$D$ ordinary vertices of the random bipartite graph used in the hardness reduction, in terms of which the phases of the gadget are expressed.
--
--   **Formalization Note** $\Psi$ is the published `BipColorHard.psi` (real `sSup` over $\Xi$, which is the maximum on feasible pairs) and the set of global maximizers is the published `psiMaxSet`, over feasible pairs of probability vectors. Both clauses of the source ($q\ge5$, $D=q+1$; $q=3$, $D=5$) are the single statement for $k\ge1$ with $D$ = `bipDeg (2k+1)`. The count is stated as `ncard` of the maximizer set.
--
--   Differences from the source:
--   - encoding: Ψ = −∞ off its domain, maximizers over the domain of Ψ → the published psiMaxSet, maximizers over the feasible pairs of probability vectors; reason: the published psi is 0 on infeasible pairs, so the domain restriction is built into psiMaxSet; same set.
--   - encoding: two clauses (odd q = 2k+1 ≥ 5 with D = q+1; q = 3, D = 5, k = 1) → one statement for every k ≥ 1 with D = bipDeg (2k+1); reason: bipDeg 3 = 5 and bipDeg q = q + 1 otherwise, so k = 1 is the second clause and k ≥ 2 the first.
--   - encoding: "precisely the following 2 C(q,k) pairs" → set equality together with ncard = 2 · C(2k+1, k); reason: the two together say the listed pairs are the maximizers and are pairwise distinct.
--   - encoding: δ, δ̂ "depending only on q" → ∃ δ δ̂ chosen after k and before S; reason: the same quantifier order.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Theorem 27, p.31 (PDF p.33); Ψ in §A.1, p.46 (PDF p.48); q = 3 in Appendix B.2, p.55 (PDF p.57)

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_RandomGraph
import Definitions.Def_BipColorHard_Supplement_Pairs

set_option autoImplicit false

namespace BipColorHard.Supplement

/-- **Theorem 27**, p.31 (PDF p.33), Galanis, Guo, He, Štefankovič, Vigoda, manuscript of Nov. 3, 2026
(sha256 78a66d1f…). Let `q = 2k + 1` and `D = bipDeg q` (`D = q + 1` for `q ≥ 5`; `D = 5` for `q = 3`, `k = 1`).
There are constants `δ, δ̂ > 0`, depending only on `q`, such that the global maximizers of `Ψ` are precisely the
`2 C(q, k)` pairs `(α^S, β^S)` and `(β^S, α^S)`, `S` a `k`-subset of `[q]`, where `α^S = alphaS k δ S` and
`β^S = betaS k δ̂ S` are positive probability vectors.

**Formalization Note.** `Ψ` is the published `psi` and its set of global maximizers is the published `psiMaxSet`,
taken over the feasible pairs of probability vectors (the domain of `Ψ`, §A.1, p.46 (PDF p.48)). The count
`2 C(q, k)` is stated as `ncard`. Coordinate sums `1` follow from `|S| = k`; positivity is part of the conclusion. -/
theorem theorem_27 (k : ℕ) (hk : 1 ≤ k) :
    ∃ δ δh : ℝ, 0 < δ ∧ 0 < δh ∧
      (∀ (S : Omega k) (i : Fin (2 * k + 1)), 0 < alphaS k δ S i ∧ 0 < betaS k δh S i) ∧
      psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1)) =
        {φ | ∃ S : Omega k, φ = (alphaS k δ S, betaS k δh S) ∨ φ = (betaS k δh S, alphaS k δ S)} ∧
      (psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1))).ncard = 2 * Nat.choose (2 * k + 1) k := by sorry

end BipColorHard.Supplement
