-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_unbiased_iff_polynomial
-- name    : FiniteSampleDependence.Rigidity.Supplement.unbiased_iff_polynomial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:50:37.647553+00:00
-- url     : https://prove2.me/theorems/37232ac5-35f1-4582-a933-991aa16ad9c6
-- title:
--   Proposition 2.4 — $d$-sample unbiased estimability on $\Delta(Z)$ iff representation by a polynomial of degree $\le d$
-- statement:
--   Let $Z$ be a finite set, $\Delta(Z)=\{P:Z\to\mathbb R\mid P\ge0,\ \sum_zP(z)=1\}$ its probability simplex, $d\in\mathbb N$, and $F$ a real functional on $\Delta(Z)$. The following are equivalent:
--
--   1. $F$ is $d$-sample unbiasedly estimable: there is a statistic $\hat F:Z^d\to\mathbb R$ with
--   $$\sum_{z\in Z^d}\hat F(z_1,\dots,z_d)\prod_{t=1}^dP(z_t)=F(P)\qquad\text{for every }P\in\Delta(Z);$$
--   2. $F$ is represented on $\Delta(Z)$ by a polynomial of degree at most $d$: there is a real polynomial $Q$ in the variables $(P(z))_{z\in Z}$ of total degree at most $d$ with $Q(P)=F(P)$ for every $P\in\Delta(Z)$.
--
--   This is Hoeffding's characterization of fixed-sample unbiased estimability; in the paper it converts degree lower bounds into lower bounds on the number of samples or tasks.
--
--   Differences from the source:
--   - encoding: E_P[F̂(Z_1,…,Z_d)] with Z_1,…,Z_d i.i.d. from P → the exact finite sum Σ_{z ∈ Z^d} F̂(z) ∏_t P(z_t); reason: for a finite Z the expectation is this sum
--   - encoding: a finite set Z → a type Z with Fintype and DecidableEq instances; reason: decidable equality is available classically for every type; it only lets the sum over Z^d be formed
--   - encoding: a polynomial of degree at most d in the probabilities P(z) → Q : MvPolynomial Z ℝ with Q.totalDegree ≤ d, evaluated at P; reason: polynomials in the variables P(z), z ∈ Z, with degree the total degree
--   - encoding: a functional F : Δ(Z) → ℝ on the simplex → a function F : (Z → ℝ) → ℝ, of which only the values on Δ(Z) (Mathlib's stdSimplex ℝ Z) enter; reason: both sides of the equivalence read F only at points of Δ(Z); every functional on Δ(Z) extends
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Proposition 2.4, PDF p. 7 (printed p. 6); Definition 2.3, same page

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model

namespace FiniteSampleDependence.Rigidity.Supplement

/-- Proposition 2.4 (Polynomial characterization [Hoe84]), PDF p. 7 (printed p. 6). For a finite
set `Z` and `d ∈ ℕ`, a functional on `Δ(Z)` is `d`-sample unbiasedly estimable if and only if it
is represented on that simplex by a polynomial of degree at most `d` in the probabilities
`P(z)`. -/
theorem unbiased_iff_polynomial (Z : Type) [Fintype Z] [DecidableEq Z] (d : ℕ)
    (F : (Z → ℝ) → ℝ) :
    UnbiasedlyEstimable Z d F ↔ PolyRepresentable Z d F := by sorry

end FiniteSampleDependence.Rigidity.Supplement
