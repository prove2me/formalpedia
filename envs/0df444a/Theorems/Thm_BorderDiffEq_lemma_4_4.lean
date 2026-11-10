-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_4_4
-- name    : BorderDiffEq.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:51.852273+00:00
-- url     : https://prove2.me/theorems/8bd6b39e-4004-4680-a8f6-183209e98d6e
-- title:
--   Lemma 4.4 — among the maximal minors of $(D^jS_i)$, the Wronskian has the least $\varepsilon$-valuation
-- statement:
--   Let $F$ be a field of characteristic zero, $S_1,\dots,S_r$ polynomials in $(y,z,x)$ with coefficients in $F((\varepsilon))$, $D=\partial/\partial z$, and let $M$ be the $r\times(r+1)$ matrix with rows $(S_i,DS_i,\dots,D^rS_i)$. For $0\le i\le r$ let $A_i=(-1)^i\det(M_{i+1})$, where $M_{i+1}$ is $M$ without its $(i+1)$-st column. If $S_1,\dots,S_r$ are linearly independent over $F((\varepsilon))(y,x)$, then for every $0\le i\le r$
--   $$
--   \mathrm{val}_\varepsilon(A_i)\ \ge\ \mathrm{val}_\varepsilon(A_r)\ =\ \mathrm{val}_\varepsilon\big(W(S_1,\dots,S_r)\big).
--   $$
--   This lets the paper divide its differential equation by $\varepsilon^{\mathrm{val}_\varepsilon(A_r)}$ and pass to the limit $\varepsilon\to0$ (Lemma 5.1 (3)).
--
--   **Formalization Note** $\mathrm{val}_\varepsilon$ of a polynomial is the least power of $\varepsilon$ in its coefficients (`epsVal`); $A_i$ is `signedMinor (derivMatrix S) i`.
--
--   Differences from the source:
--   - generalization: constants in $F(\varepsilon)$ → constants in $F((\varepsilon))$ (`LaurentSeries F`); reason: $F(\varepsilon)\subset F((\varepsilon))$ and $\mathrm{val}_\varepsilon$, $\lim_{\varepsilon\to0}\varepsilon^{-m}$ restrict to the paper's; the source's instances are instances of the Lean statement
--   - encoding: polynomials in $F(\varepsilon)[y,z,x]$, independence over $F(\varepsilon,y,x)$ → `Polynomial` in $z$ over `MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F)`, independence over that coefficient ring; reason: independence over a domain equals independence over its fraction field (clear denominators), and independence of vectors with coordinates in a field is unchanged by a field extension
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.4, p.25

import Mathlib
import Definitions.Def_BorderDiffEq_wronskian
import Definitions.Def_BorderDiffEq_derivMatrix
import Definitions.Def_BorderDiffEq_signedMinor
import Definitions.Def_BorderDiffEq_epsVal

namespace BorderDiffEq

/-- **Lemma 4.4 (the Wronskian has the least `ε`-valuation among the maximal minors)**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), Lemma 4.4, p.25). Let
`S₁, …, S_r ∈ F(ε)[y, z, x]`, let `M` be the `r × (r+1)` matrix with rows
`(Sᵢ, D Sᵢ, …, D^r Sᵢ)`, `D = ∂_z`, and `Aᵢ = (-1)^i det(M_{i+1})` for `0 ≤ i ≤ r`. If
`S₁, …, S_r` are linearly independent over `F(ε, y, x)`, then
`val_ε(Aᵢ) ≥ val_ε(A_r) = val_ε(W(S₁, …, S_r))` for every `i`.

**Formalization Note.** `F` is any field of characteristic zero (standing assumption, p.23); `F(ε)` is
generalized to `F((ε))` (`LaurentSeries F`). A polynomial in `(y, z, x)` is a polynomial in `z` over
`MvPolynomial (Fin n ⊕ Fin n) F((ε))` (`y = Sum.inl`, `x = Sum.inr`). Linear independence over
`F((ε))(y, x)` is stated over the coefficient ring `MvPolynomial (Fin n ⊕ Fin n) F((ε))`, which is
equivalent (clear denominators). `Aᵢ` is `signedMinor (derivMatrix S) i` (0-based columns). -/
theorem lemma_4_4 (F : Type) [Field F] [CharZero F] (n r : ℕ)
    (S : Fin r → Polynomial (MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F)))
    (hS : LinearIndependent (MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F)) S) :
    (∀ i : Fin (r + 1),
      epsVal (signedMinor (derivMatrix S) (Fin.last r)) ≤ epsVal (signedMinor (derivMatrix S) i)) ∧
    epsVal (signedMinor (derivMatrix S) (Fin.last r)) = epsVal (wronskian S) := by sorry

end BorderDiffEq
