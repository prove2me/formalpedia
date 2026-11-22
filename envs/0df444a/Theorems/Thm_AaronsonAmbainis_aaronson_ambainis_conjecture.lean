-- Prove2me | Theorems.Thm_AaronsonAmbainis_aaronson_ambainis_conjecture
-- name    : AaronsonAmbainis.aaronson_ambainis_conjecture
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-07T07:40:56.156721+00:00
-- url     : https://prove2.me/theorems/1433ae6d-fabb-4836-baf4-d7a913377b3c
-- title:
--   Aaronson--Ambainis conjecture: bounded low-degree polynomials have an influential variable
-- statement:
--   Let $p:\mathbb{R}^N\to\mathbb{R}$ be a real multivariate polynomial of degree at most $d$, viewed as a function on the Boolean cube $\{0,1\}^N$ under the uniform distribution, with $\mathbb{E}[\cdot]$, $\operatorname{Var}[\cdot]$ and $\operatorname{Inf}_i[\cdot]$ as in the imported definitions.
--
--   The conjecture asserts that boundedness together with low degree forces some single coordinate to carry a polynomially large share of the function's variance. Precisely, there is an absolute constant $C$ such that the following holds for every $N$, every $d$, every such $p$ and every $\varepsilon$: if
--
--   1. $0\le p(x)\le 1$ for every $x\in\{0,1\}^N$,
--   2. $\deg p\le d$, and
--   3. $\operatorname{Var}[p]\ge\varepsilon>0$,
--
--   then there exists a coordinate $i$ with
--
--   $$\operatorname{Inf}_i[p]\;\ge\;\Big(\frac{\varepsilon}{d}\Big)^{C}.$$
--
--   The conjecture is the open problem at the centre of Aaronson and Ambainis's case that quantum speedups require structure: they prove that it would imply every bounded-error quantum algorithm making $T$ queries to a Boolean input can be simulated on most inputs, to small error, by a classical algorithm making $\mathrm{poly}(T)$ queries. Note that the constant $C$ is quantified outermost, so it may not depend on $N$, $d$, $\varepsilon$ or $p$; that uniformity is the whole content, since bounds degrading exponentially in $d$ are known.
--
--   **Formalization Note** Three choices are worth flagging. Boundedness is asserted only at cube points, not on all of $\mathbb{R}^N$, matching the source. The source's exact-degree hypothesis is rendered as `p.totalDegree ≤ d` universally quantified over $d$; this is equivalent, because the smallest admissible $d$ yields the strongest bound. The source's exponent $O(1)$ is rendered as an existentially quantified `C : ℕ` with no leading multiplicative constant, since admitting one would weaken the claim. A fourth point concerns the degree hypothesis: `MvPolynomial.totalDegree` is the *syntactic* total degree of the representative polynomial, not the degree of the function it induces on the cube. Since $\operatorname{Var}$ and $\operatorname{Inf}_i$ depend on $p$ only through its $2^N$ values at cube points, the polynomial $X_1^{17}$ induces the same cube function as $X_1$ while having total degree $17$. This does not change the statement's content. Multilinear reduction never raises degree, because a monomial of total degree $t$ involves at most $t$ distinct variables, so the multilinear degree of the induced function is at most `totalDegree`; conversely every cube function has a multilinear representative whose `totalDegree` equals its multilinear degree, and that representative is itself an admissible instance. The formalization is therefore equivalent to the reading in which $d$ bounds the multilinear degree. Solvers should nonetheless expect to pass to the multilinear representative before using the degree hypothesis.
-- source:
--   Aaronson & Ambainis, The Need for Structure in Quantum Speedups, arXiv:0911.0996, Conjecture 6 ("Bounded Polynomials Have Influential Variables")

import Definitions.Def_AaronsonAmbainis

namespace AaronsonAmbainis

theorem aaronson_ambainis_conjecture :
    ∃ C : ℕ, ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (ε : ℝ),
      p.totalDegree ≤ d →
      (∀ x : Fin N → Bool, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1) →
      0 < ε → ε ≤ cubeVar p →
      ∃ i : Fin N, (ε / (d : ℝ)) ^ C ≤ cubeInfl p i := by sorry

end AaronsonAmbainis
