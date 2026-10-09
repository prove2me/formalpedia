-- Prove2me | Theorems.Thm_BanditCovariates_ABSE_bound_5_10
-- name    : BanditCovariates.ABSE.bound_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:09:25.471986+00:00
-- url     : https://prove2.me/theorems/3dfb157e-76e9-45eb-a603-20828a60387e
-- title:
--   (5.10), p. 26 — an arm outside Ī_B is separated from ı̌ by (3/2)ε_{B,ℓ_B} in cell means
-- statement:
--   Let the arm means $f^{(1)},\dots,f^{(K)}$ be measurable, $[0,1]$-valued and $(\beta,L)$-Hölder on $\mathcal X=[0,1]^d$ for the Euclidean norm, with $d\ge1$, $0<\beta\le1$, $L>0$, and let the covariate law $P_X$ have a density bounded below by $\underline c>0$ on $\mathcal X$. Put $c_0=2Ld^{\beta/2}$. Let $B$ be a dyadic cell, $n$ a horizon, and $\ell_B$, $\varepsilon_{B,\ell_B}=2U(\ell_B,n|B|^d)$ as in (5.2). Suppose arm $i$ and a point $x\in B$ satisfy $f^\star(x)-f^{(i)}(x)>8c_0|B|^\beta$ (so $i\notin\bar{\mathcal I}_B$), and arm $\check\imath$ attains the maximum at $x$: $f^\star(x)=f^{(\check\imath)}(x)$. Then
--
--   $$\bar f_B^{(\check\imath)}\ge f^{(\check\imath)}(x)-c_0|B|^\beta>f^{(i)}(x)+7c_0|B|^\beta\ge\bar f_B^{(i)}+6c_0|B|^\beta\ge\bar f_B^{(i)}+\tfrac32\varepsilon_{B,\ell_B}.$$
--
--   This deterministic separation is what makes successive elimination on $B$ discard every arm outside $\bar{\mathcal I}_B$ within $\ell_B$ rounds, unless the empirical means leave their confidence intervals.
--
--   **Formalization Note** All four links of the chain are stated. The last uses the definition (5.2) of $\ell_B$, i.e. $\varepsilon_{B,\ell_B}\le4c_0|B|^\beta$. The density lower bound guarantees $P_X(B)>0$, so the cell means are genuine averages.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 26, (5.10)

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_Cells

noncomputable section

namespace BanditCovariates.ABSE

/-- Display (5.10), p. 26: if arm `i` has a gap larger than `8c₀|B|^β` at some
point `x` of the cell `B`, and arm `iMax` (the page's ı̌) attains `f⋆(x)`, then the cell means of the
two arms are separated by at least `(3/2) ε_{B,ℓ_B}`. All four links of the chain. -/
theorem bound_5_10 {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (β L cLow cHigh : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 < L) (hcLow : 0 < cLow)
    (M : Machine d K Ω) (hM : IsMachine M) (hdens : HasDensityBounds M cLow cHigh)
    (hHolder : IsHolder M β L)
    (B : Cell d) (hB : ValidCell B)
    (i iMax : Fin K) (x : Covariate d) (hx : x ∈ cellSet B)
    (hgap : fStar M x - M.f i x > 8 * c0 d β L * side B ^ β)
    (hiMax : fStar M x = M.f iMax x) :
    fbar M B iMax ≥ M.f iMax x - c0 d β L * side B ^ β ∧
    M.f iMax x - c0 d β L * side B ^ β > M.f i x + 7 * c0 d β L * side B ^ β ∧
    M.f i x + 7 * c0 d β L * side B ^ β ≥ fbar M B i + 6 * c0 d β L * side B ^ β ∧
    fbar M B i + 6 * c0 d β L * side B ^ β ≥
      fbar M B i + 3 / 2 * epsilon d n B (ell d n β L B) := by sorry

end BanditCovariates.ABSE
