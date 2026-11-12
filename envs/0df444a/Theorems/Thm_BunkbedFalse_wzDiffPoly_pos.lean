-- Prove2me | Theorems.Thm_BunkbedFalse_wzDiffPoly_pos
-- name    : BunkbedFalse.wzDiffPoly_pos
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T00:08:10.513697+00:00
-- url     : https://prove2.me/theorems/7bdccda6-d6b7-47fc-937c-eafb70cef4b3
-- title:
--   Positivity of the Wierman--Ziff difference polynomial
-- statement:
--   This is the arithmetic half of the robustness lemma (Lemma 3.3) of Gladkov--Pak--Zimin, stated as a self-contained inequality with no probability theory in it.
--
--   Let $x, y, z, u$ be nonnegative rationals with
--   $$x + y + z + 2u = 1,$$
--   and set
--   $$W \;=\; xy - u^{2}.$$
--   Assume that $W > 0$ and that
--   $$400\,z \;\le\; W. \tag{1}$$
--   Then the explicit degree-$12$ polynomial $\texttt{wzDiffPoly}(x,y,z,u)$ of the $\texttt{BunkbedWZPoly}$ definition is strictly positive.
--
--   **Interpretation of the hypotheses.** The variables are the state probabilities of the Wierman--Ziff model in its symmetric case, $x = P_{abc}$, $y = P_{a|b|c}$, $z = P_{a|bc}$ and $u = P_{ab|c} = P_{ac|b}$, so the normalisation $x + y + z + 2u = 1$ says exactly that $P$ is a probability distribution, and $(1)$ is Eq. [1] of the source. The quantity $W$ is the determinant-like expression $P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$, which is nonnegative for any hyperedge simulated by a gadget in Bernoulli percolation, by the Harris--Kleitman inequality.
--
--   The hypothesis $W > 0$ is genuinely needed and does not follow from $(1)$. If $z = 0$ and $W = 0$, then $(1)$ holds as $0 \le 0$, yet the two connection probabilities coincide exactly, so the strict inequality fails. The family $x = w^2$, $y = (1-w)^2$, $u = w(1-w)$, $z = 0$ satisfies every other hypothesis and makes $W = 0$ identically.
--
--   **Mathematical role.** Together with the companion statement `BunkbedFalse.wz_diff_poly`, which identifies the difference of the two connection probabilities with this polynomial, it yields Lemma 3.3. The mechanism is that $\texttt{wzDiffPoly}$ has leading term $W^6$ and the coefficient of $z^j$ carries a factor $W^{6-j}$, so under $(1)$ every correction term is smaller than the leading term by a factor of order $400^{-j}$; positivity then follows with a wide margin, the total correction amounting to less than four percent of $W^6$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Lemma 3.3 (p. 3) and Sections 3.3-3.6 (pp. 3-6).

import Definitions.Def_BunkbedWZPoly
open Bunkbed Bunkbed.Hyper

namespace BunkbedFalse

/-- **Positivity of the Wierman-Ziff difference polynomial.** The arithmetic half of Lemma 3.3
of Gladkov-Pak-Zimin: on the region of the simplex cut out by Eq. [1] together with strict
positivity of the determinant `x * y - u ^ 2`, the explicit degree-12 polynomial
`wzDiffPoly` is strictly positive. -/
theorem wzDiffPoly_pos (x y z u : ℚ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u)
    (hsum : x + y + z + 2 * u = 1)
    (hpos : 0 < x * y - u * u)
    (h400 : 400 * z ≤ x * y - u * u) :
    0 < wzDiffPoly x y z u := by
  sorry

end BunkbedFalse
