-- Prove2me | Theorems.Thm_BoundEntGauss_family_construction
-- name    : BoundEntGauss.family_construction
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:03.541061+00:00
-- url     : https://prove2.me/theorems/9a73275d-55f8-454d-be40-8507b895e8c5
-- title:
--   Section IV, Eq. (11) — the construction from $\Omega_1$ determines $\gamma(a,b,c,e,f)$ and requires $d=(bc+f)/a$
-- statement:
--   Let $a,b,c,d,e,f>0$ with $a\ne ce$, and let $\Omega_1=(-a,ib,c,-id,e,-if,1,0)$ as in (11). For a real $8\times8$ matrix $\gamma$ on the $2\times2$-mode phase space the following are equivalent:
--
--   1. $\gamma$ is symmetric, commutes with $S$, $C$ and $R$, and $\Omega_1$ lies in the null space of $\gamma+i\sigma$, i.e. $(\gamma+i\sigma)\Omega_1=0$;
--   2. $ad=bc+f$ and $\gamma=\gamma(a,b,c,e,f)$, the closed form of the family.
--
--   This is the paper's construction of the family: commuting with $R$, $C$, $S$ fixes $\gamma$ on the eight vectors obtained from $\Omega_1$, which form a basis exactly when $a\ne ce$, and "$\gamma$ being real and symmetric requires $d=(bc+f)/a$". The theorem identifies the explicit matrix used by the goal with the matrix the paper constructs.
--
--   Differences from the source:
--   - encoding: γ defined by the construction γ = ΛΩ⁻¹ from Ω₁ of (11), with d = (bc+f)/a → the closed form wwGamma a b c e f, tied to the construction by the milestone family_construction; reason: an explicit matrix instead of an opaque inverse; same matrix
--   - encoding: γ = ΛΩ⁻¹ with Ω the matrix of the eight vectors TΩ₁, Λ_k = γΩ_k → the conditions defining that γ (symmetric, commuting with S, C, R, (γ + iσ)Ω₁ = 0), stated without a matrix inverse; reason: equivalent when Ω is invertible, i.e. when a ≠ ce
--   - encoding: d = (bc+f)/a; equality a = ce "ruled out" → a·d = b·c + f; hypothesis a ≠ c·e; reason: division-free form; a ≠ ce only excludes the case det Ω = 0 where the construction is undefined
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, Eq. (11), p. 4

import Mathlib
import Definitions.Def_BoundEntGauss_totalSigma
import Definitions.Def_BoundEntGauss_opS
import Definitions.Def_BoundEntGauss_opC
import Definitions.Def_BoundEntGauss_opR
import Definitions.Def_BoundEntGauss_omegaOne
import Definitions.Def_BoundEntGauss_wwGamma

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (covarianceBlockMatrix)

namespace BoundEntGauss

/-- **The construction from Ω₁ of Eq. (11) determines γ, and forces d = (bc + f)/a.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, Eq. (11), p. 4: "We start with a generic vector Ω₁ = (−a, ib, c, −id, e, −if, 1, 0),
a, b, …, f > 0. (11) Then γ being real and symmetric requires d = (bc + f)/a".

Let `a, b, c, d, e, f > 0` with `a ≠ c·e`. A real `8 × 8` matrix `γ` on the `2 × 2`-mode phase
space is symmetric, commutes with `S`, `C` and `R`, and has `Ω₁` in the null space of `γ + iσ`
if and only if `a·d = b·c + f` and `γ` is the matrix `γ(a, b, c, e, f)` (`wwGamma`).

**Formalization Note.** This is the paper's construction `γ = Λ Ω⁻¹` stated without a matrix
inverse: commuting with `R, C, S` and `(γ + iσ)Ω₁ = 0` fix `γ` on the eight vectors `T Ω₁`, which
form a basis exactly when `a ≠ c·e` (the paper: equality "would be equivalent to det(Ω) = 0"). The
relation `d = (b·c + f)/a` is written `a·d = b·c + f`. -/
theorem family_construction (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f) (hace : a ≠ c * e)
    (Γ : Matrix (QuadratureIndex 2 ⊕ QuadratureIndex 2) (QuadratureIndex 2 ⊕ QuadratureIndex 2) ℝ) :
    (Γ.transpose = Γ ∧ opS * Γ = Γ * opS ∧ opC * Γ = Γ * opC ∧ opR * Γ = Γ * opR ∧
        (complexify Γ + Complex.I • complexify (totalSigma 2 2)).mulVec (omegaOne a b c d e f) = 0) ↔
      (a * d = b * c + f ∧ Γ = covarianceBlockMatrix (wwGamma a b c e f)) := by sorry

end BoundEntGauss
