-- Prove2me | Theorems.Thm_AaronsonAmbainis_nisan_szegedy_relevant_card_le_of_boolean_valued
-- name    : AaronsonAmbainis.nisan_szegedy_relevant_card_le_of_boolean_valued
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-07T21:28:38.259645+00:00
-- url     : https://prove2.me/theorems/f1b24281-5c01-4073-b5e9-a9dcbfcf39b8
-- title:
--   Nisan--Szegedy: a Boolean-valued degree-$k$ function is a $k2^{k-1}$-junta
-- statement:
--   Call a coordinate $i$ **relevant** for $p$ when $\operatorname{Inf}_i[p]>0$, that is, when flipping the $i$-th bit changes the value of $p$ somewhere on the cube. The Nisan--Szegedy theorem bounds the number of relevant coordinates of a Boolean-valued function by a quantity depending on its degree alone, with no reference to the number of variables $N$:
--
--   $$\#\{\,i:\operatorname{Inf}_i[p]>0\,\}\;\le\;k\,2^{\,k-1}$$
--
--   for every $p$ of degree at most $k$ taking only the values $0$ and $1$ on $\{0,1\}^N$. Equivalently, such a $p$ depends on at most $k2^{k-1}$ of its variables -- it is a $k2^{k-1}$-junta.
--
--   This is the result that settles the Aaronson--Ambainis conjecture for Boolean-valued functions: a function with boundedly many relevant coordinates must have a coordinate carrying a constant fraction of its variance. The conjecture's difficulty is that the junta conclusion fails once the range is relaxed from $\{0,1\}$ to the interval $[0,1]$, where a low-degree function may depend on all $N$ variables.
--
--   The bound $k2^{k-1}$ cannot be improved substantially; the source records a matching example.
--
--   **Formalization Note** The source works with $\pm1$-valued functions on $\{-1,1\}^n$, whereas the hypothesis here is that $p$ takes only the values $0$ and $1$ at cube points. The two are related by $g=1-2p$, which is $\pm1$-valued, has the same degree as $p$, and satisfies $\operatorname{Inf}_i[g]=4\operatorname{Inf}_i[p]$ in the normalisation used here. O'Donnell's total influence $I[g]=\sum_i\mathbb{E}[(D_ig)^2]$ is one quarter of $\sum_i\operatorname{Inf}_i[g]$, hence equal to $\sum_i\operatorname{Inf}_i[p]$; and $\operatorname{Inf}_i[g]>0$ exactly when $\operatorname{Inf}_i[p]>0$, so the set of relevant coordinates is the same for both. The degree hypothesis is on `totalDegree`, the syntactic degree of the representative, which bounds the multilinear degree from above -- the safe direction here.
-- source:
--   O'Donnell, Analysis of Boolean Functions, Cambridge Univ. Press 2014; corrected version arXiv:2105.10386, Theorem 3.4 (p. 70): "Suppose f : {-1,1}^n -> {-1,1} has deg(f) <= k. Then f is a k*2^(k-1)-junta", with the relevant-coordinate count given in its proof discussion (p. 71). Attributed there (Chapter 3 notes, p. 91) to N. Nisan and M. Szegedy, On the degree of Boolean functions as real polynomials, Computational Complexity 4(4):301-313, 1994.

import Definitions.Def_AaronsonAmbainis

namespace AaronsonAmbainis

theorem nisan_szegedy_relevant_card_le_of_boolean_valued
    (N k : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hdeg : p.totalDegree ≤ k)
    (hbool : ∀ x : Fin N → Bool, cubeEval p x = 0 ∨ cubeEval p x = 1) :
    (Finset.univ.filter (fun i : Fin N => 0 < cubeInfl p i)).card ≤ k * 2 ^ (k - 1) := by sorry

end AaronsonAmbainis
