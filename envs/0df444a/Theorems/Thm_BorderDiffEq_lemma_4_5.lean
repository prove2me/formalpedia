-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_4_5
-- name    : BorderDiffEq.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:10.700644+00:00
-- url     : https://prove2.me/theorems/24e2cf87-17c2-4d82-9fd8-bc75d73d6291
-- title:
--   Lemma 4.5 — the lowest $\varepsilon$-coefficient of $W(\Phi_y(T_1),\dots,\Phi_y(T_r))$ is nonzero at $z=0$
-- statement:
--   Let $F$ be a field of characteristic zero, $T_1,\dots,T_r$ polynomials in $x$ with coefficients in $F((\varepsilon))$, and $S_i:=\Phi_y(T_i)=T_i(y+zx)$. Suppose $W(S_1,\dots,S_r)\neq0$, let $m:=\mathrm{val}_\varepsilon(W(S_1,\dots,S_r))$ and write
--   $$
--   W(S_1,\dots,S_r)=\varepsilon^m\big(W_0(y,z,x)+\varepsilon W'\big),
--   $$
--   with $W_0$ free of $\varepsilon$ (so $W_0\ne0$) and $\mathrm{val}_\varepsilon(W')\ge0$. Then
--   $$
--   W_0(y,0,x)\neq0 .
--   $$
--   This gives the nonvanishing $b_r(y,0,x)\ne0$ of the leading coefficient in Lemma 5.1.
--
--   **Formalization Note** $W_0$ is `epsCoeff m W`, the coefficient of $\varepsilon^m$, which is exactly the decomposition above; $W_0(y,0,x)$ is `Polynomial.eval 0`.
--
--   Differences from the source:
--   - generalization: constants in $F(\varepsilon)$ → constants in $F((\varepsilon))$ (`LaurentSeries F`); reason: $F(\varepsilon)\subset F((\varepsilon))$ and $\mathrm{val}_\varepsilon$, $\lim_{\varepsilon\to0}\varepsilon^{-m}$ restrict to the paper's; the source's instances are instances of the Lean statement
--   - encoding: $W=\varepsilon^m(W_0+\varepsilon W')$ with $W_0$ $\varepsilon$-free and $\mathrm{val}_\varepsilon(W')\ge0$ → $W_0:=$ the $\varepsilon^m$-coefficient of $W$, with $m$ given by $\mathrm{val}_\varepsilon(W)=m$; reason: the decomposition determines $W_0$ as that coefficient
--   - encoding: polynomials in $F(\varepsilon)[y,z,x]$ → `Polynomial` in $z$ over `MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F)`; reason: a polynomial in $(y,z,x)$ is a polynomial in $z$ over the polynomials in $(y,x)$
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.5, p.26

import Mathlib
import Definitions.Def_BorderDiffEq_shift
import Definitions.Def_BorderDiffEq_wronskian
import Definitions.Def_BorderDiffEq_epsVal
import Definitions.Def_BorderDiffEq_epsCoeff

namespace BorderDiffEq

/-- **Lemma 4.5 (the lowest `ε`-coefficient of the Wronskian is nonzero at `z = 0`)**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), Lemma 4.5, p.26). Let
`T₁, …, T_r ∈ F(ε)[x]` and `Sᵢ := Φ_y(Tᵢ)`. Suppose `W(S₁, …, S_r) ≠ 0`, let
`m := val_ε(W(S₁, …, S_r))` and write `W(S₁, …, S_r) = ε^m (W₀(y, z, x) + ε W')` with `W₀` free of
`ε` and `val_ε(W') ≥ 0`. Then `W₀(y, 0, x) ≠ 0`.

**Formalization Note.** `F` is any field of characteristic zero; `F(ε)` is generalized to
`F((ε))`. `W₀` is the `ε^m`-coefficient `epsCoeff m W`, which is exactly the paper's
decomposition; `W₀(y, 0, x)` is its value at `z = 0` (`Polynomial.eval 0`). `m` is the (finite)
valuation of the nonzero `W`. -/
theorem lemma_4_5 (F : Type) [Field F] [CharZero F] (n r : ℕ)
    (T : Fin r → MvPolynomial (Fin n) (LaurentSeries F))
    (hW : wronskian (fun i => shift (T i)) ≠ 0) (m : ℤ)
    (hm : epsVal (wronskian (fun i => shift (T i))) = m) :
    (epsCoeff m (wronskian (fun i => shift (T i)))).eval 0 ≠ 0 := by sorry

end BorderDiffEq
