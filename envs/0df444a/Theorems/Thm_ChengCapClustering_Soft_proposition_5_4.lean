-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_proposition_5_4
-- name    : ChengCapClustering.Soft.proposition_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:25.923175+00:00
-- url     : https://prove2.me/theorems/5ae9cf2e-2be7-47dc-8cc6-f9960eb88492
-- title:
--   Proposition 5.4 — the constant $\beta^*_z$: (a) dual characterization, (b) $\beta^*_z<3^z$, $\beta^*_1=3$, $\beta^*_2=5$ and three numerical values, (c) sharpness for movability
-- statement:
--   Let $z\ge1$. (a) $\beta^*_z=\sup\mathbb E|1+\xi|^z$, the supremum over all real random variables $\xi$ with finite support, $\mathbb E[\xi]=0$ and $\mathbb E|\xi|^z=2^z$. (b) $\beta^*_z<3^z$ for every $z>1$; moreover $\beta^*_1=3$, $\beta^*_2=5$, $\beta^*_{3/2}\approx4.1397$, $\beta^*_3\approx16.8308$ and $\beta^*_4\approx53.4056$. (c) For all $u\ge1$ and $v\ge0$ with $u+2^zv<\beta^*_z$, there is a finite set $Q\subset\mathbb R$ such that the block $Q$ with an optimal center of $Q$ as its representative is not $(u,v)$-movable.
--
--   Differences from the source:
--   - encoding: real random variables ξ with finite support; the supremum → finite lists of values t_i with probabilities w_i ≥ 0 summing to 1; IsLUB of the set of values of E|1+ξ|^z; reason: a finite-support law is such a list; IsLUB states that the supremum exists and equals β*_z
--   - reading: β*_{3/2} ≈ 4.1397, β*_3 ≈ 16.8308, β*_4 ≈ 53.4056 → |β* − x| ≤ 5·10⁻⁵ for each printed value x (equality after rounding to four decimals); reason: the printed values have four decimals; checked numerically (two-point dual laws and matching certificates give 4.139656, 16.830827, 53.405588)
--   - reading: "the block Q with an optimal center of Q as its representative is not (u, v)-movable" → ∃ finite Q ⊂ ℝ such that for every minimizer a of c ↦ ∑_{q∈Q}|q−c|^z, Q with representative a is not (u, v)-movable (slots anywhere in ℝ); reason: for z = 1 optimal centers need not be unique; the stronger reading (every optimal center) is taken
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Proposition 5.4, printed p. 28 / PDF p. 30; proof in Appendix A, printed pp. 44–46

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Certificate

namespace ChengCapClustering.Soft

/-- Proposition 5.4 (The constant `β*_z`), printed p. 28 / PDF p. 30.
(a) For `z ≥ 1`, `β*_z` is the supremum of `E|1 + ξ|^z` over real random variables `ξ` with finite
support, `E[ξ] = 0` and `E|ξ|^z = 2^z` (a finite-support law is a list of values `t` with
probabilities `w`).
(b) `β*_z < 3^z` for every `z > 1`; `β*_1 = 3`, `β*_2 = 5`, `β*_{3/2} ≈ 4.1397`, `β*_3 ≈ 16.8308` and
`β*_4 ≈ 53.4056`, each `≈` read as "equal after rounding to four decimals" (`|β − x| ≤ 5·10⁻⁵`).
(c) For `z ≥ 1`, `u ≥ 1`, `v ≥ 0` with `u + 2^z v < β*_z`, some finite set `Q ⊂ ℝ` is not
`(u, v)`-movable with an optimal center of `Q` as its representative (whichever optimal center). -/
theorem proposition_5_4 :
    (∀ z : ℝ, 1 ≤ z →
      IsLUB {r : ℝ | ∃ (m : ℕ) (t w : Fin m → ℝ), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
          ∑ i, w i * t i = 0 ∧ ∑ i, w i * |t i| ^ z = (2 : ℝ) ^ z ∧
          r = ∑ i, w i * |1 + t i| ^ z}
        (betaStar z)) ∧
    ((∀ z : ℝ, 1 < z → betaStar z < (3 : ℝ) ^ z) ∧
      betaStar 1 = 3 ∧ betaStar 2 = 5 ∧
      |betaStar (3 / 2) - 4.1397| ≤ 0.00005 ∧
      |betaStar 3 - 16.8308| ≤ 0.00005 ∧
      |betaStar 4 - 53.4056| ≤ 0.00005) ∧
    ∀ z u v : ℝ, 1 ≤ z → 1 ≤ u → 0 ≤ v → u + (2 : ℝ) ^ z * v < betaStar z →
      ∃ Q : Finset ℝ, ∀ a : ℝ,
        (∀ c : ℝ, ∑ q ∈ Q, |q - a| ^ z ≤ ∑ q ∈ Q, |q - c| ^ z) →
        ¬ IsMovable z u v Set.univ Q id a := by sorry

end ChengCapClustering.Soft
