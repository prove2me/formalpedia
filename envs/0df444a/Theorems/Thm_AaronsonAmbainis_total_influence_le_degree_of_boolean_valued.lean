-- Prove2me | Theorems.Thm_AaronsonAmbainis_total_influence_le_degree_of_boolean_valued
-- name    : AaronsonAmbainis.total_influence_le_degree_of_boolean_valued
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-07T21:28:04.279732+00:00
-- url     : https://prove2.me/theorems/7f4e67be-5f13-4d4e-bfc4-3b70220863dc
-- title:
--   Total influence of a Boolean-valued function is at most its degree
-- statement:
--   Let $p$ be a real polynomial in $N$ variables of degree at most $d$ which takes only the values $0$ and $1$ at points of the cube $\{0,1\}^N$. Then its influences sum to at most its degree:
--
--   $$\sum_{i=1}^{N}\operatorname{Inf}_i[p]\;\le\;d.$$
--
--   For Boolean-valued functions the total influence is also the average sensitivity, so the statement says that a function of low degree cannot be sensitive to many coordinates on average. It is the quantitative input to the junta bound for Boolean-valued functions, and it is sharp: the dictator $p(x)=x_1$ has degree $1$ and influence sum $1$, and the parity of three bits has degree $3$ and influence sum $3$.
--
--   Boundedness in the interval $[0,1]$ is not enough for this inequality -- the hypothesis is the strictly stronger one that $p$ is $\{0,1\}$-valued on the cube. That gap is precisely what makes the Aaronson--Ambainis conjecture hard.
--
--   **Formalization Note** The source works with $\pm1$-valued functions on $\{-1,1\}^n$, whereas the hypothesis here is that $p$ takes only the values $0$ and $1$ at cube points. The two are related by $g=1-2p$, which is $\pm1$-valued, has the same degree as $p$, and satisfies $\operatorname{Inf}_i[g]=4\operatorname{Inf}_i[p]$ in the normalisation used here. O'Donnell's total influence $I[g]=\sum_i\mathbb{E}[(D_ig)^2]$ is one quarter of $\sum_i\operatorname{Inf}_i[g]$, hence equal to $\sum_i\operatorname{Inf}_i[p]$; and $\operatorname{Inf}_i[g]>0$ exactly when $\operatorname{Inf}_i[p]>0$, so the set of relevant coordinates is the same for both. The degree hypothesis is on `totalDegree`, the syntactic degree of the representative, which bounds the multilinear degree from above -- the safe direction here.
-- source:
--   O'Donnell, Analysis of Boolean Functions, Cambridge Univ. Press 2014; corrected version arXiv:2105.10386, Fact 3.7 (p. 71): "For f : {-1,1}^n -> {-1,1}, I[f] <= deg(f)"; with I[f] as Definition 2.27 and Inf_i as Definition 2.17, D_i as Definition 2.16.

import Definitions.Def_AaronsonAmbainis

namespace AaronsonAmbainis

theorem total_influence_le_degree_of_boolean_valued
    (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hdeg : p.totalDegree ≤ d)
    (hbool : ∀ x : Fin N → Bool, cubeEval p x = 0 ∨ cubeEval p x = 1) :
    ∑ i : Fin N, cubeInfl p i ≤ (d : ℝ) := by sorry

end AaronsonAmbainis
