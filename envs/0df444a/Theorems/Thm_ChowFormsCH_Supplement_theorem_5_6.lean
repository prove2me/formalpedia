-- Prove2me | Theorems.Thm_ChowFormsCH_Supplement_theorem_5_6
-- name    : ChowFormsCH.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:24:12.503281+00:00
-- url     : https://prove2.me/theorems/68f5ef49-4b7c-4355-86e5-bfba1118bd88
-- title:
--   Theorem 5.6 (= Theorem 1.9) — APS over $\mathbb{F}_{p^a}$, $\mathbb{F}_{p^a}(t_1,\dots,t_k)$, $\mathbb{Q}[\alpha]$ and $\mathbb{Q}[\alpha](t_1,\dots,t_k)$ lies in CH
-- statement:
--   Let $F$ be a field with algebraic closure $\overline{F}$. Polynomials $f_1, \dots, f_m \in F[x_1, \dots, x_n]$ are **approximately satisfiable** if the Zariski closure of the image of
--   $$\phi_f : \overline{F}^{\,n} \to \overline{F}^{\,m}, \qquad \phi_f(a) = (f_1(a), \dots, f_m(a)),$$
--   contains the origin $(0, \dots, 0)$ (Definition 1.7). The **APS problem over $F$** asks, given an algebraic circuit over $F$ that computes $f_1, \dots, f_m$, whether they are approximately satisfiable.
--
--   **Theorem 5.6.** Let $F$ be one of the fields
--
--   1. $\mathbb{F}_{p^a}$ ($p$ prime, $a \ge 1$),
--   2. $\mathbb{F}_{p^a}(t_1, \dots, t_k)$,
--   3. a number field $\mathbb{Q}[\alpha]$,
--   4. $\mathbb{Q}[\alpha](t_1, \dots, t_k)$.
--
--   Then APS over $F$ lies in CH.
--
--   Circuits may use constants from $F$, and the encoding of a circuit includes the bits of its constants; constants of a rational function field are given in the dense representation. Theorem 1.9 in the introduction states the same result. Previously APS was known to be in CH over $\mathbb{Q}$ and over finite fields; the rational function fields are new.
--
--   **Formalization Note** The statement has two parts. Part (1) covers $\mathbb{Q}$, number fields and finite fields through the published `CoefficientPresentation`, `ValidCircuit` and `PolynomialAPS`; part (2) covers $F(t_1, \dots, t_k)$ over each such $F$ and every $k \ge 0$, through a local circuit model whose constants are quotients of dense polynomials in $t$. In each part there is, for every presented field, one language in CH correct on every valid circuit, with no bound on the number of variables, outputs, degrees or size.
--
--   Differences from the source:
--
--   - reading: APS over F lies in CH, for F one of the four kinds of fields → for each presented field F separately there is one language in CH (its level may depend on F), fixed before every input of APS over F; reason: 'APS over F' is a problem for a fixed field F; the fields are given by a fixed presentation
--   - encoding: F_{p^a}, a number field ℚ[α] → the published CoefficientPresentation: F_p[U]/(μ) for a prime p and an irreducible μ (all fields F_{p^a}, a ≥ 1), ℚ[U]/(μ) for an irreducible μ (all number fields, ℚ included), and ℚ; scalars as coordinate vectors in the power basis, in binary; reason: every such field has such a presentation and every presentation is such a field
--   - encoding: F_{p^a}(t₁, …, t_k), ℚ[α](t₁, …, t_k), constants encoded in the dense representation (§5.2, p.44) → FunFieldPresentation (a base presentation and k ≥ 0), field FractionRing F[t₁, …, t_k]; a constant is a numerator and a nonzero denominator in F[t], each given densely by a degree bound and all coefficients; reason: the paper's encoding of constants of rational function fields; k = 0 is allowed and gives F again
--   - encoding: algebraic circuits with constants on the wires, |C| including the bits of the constants → circuits with constant gates (and a − gate), division gates allowed under the promise of no division by zero and polynomial outputs; the encoding includes the encodings of all constants; reason: a weighted wire is a product with a constant gate, so the two models are polynomially equivalent
--   - encoding: APS (Definition 1.7): 0 in the closure of the image of ϕ_f : Aⁿ → A^m over the algebraic closure F̄ → PolynomialAPS (published) / IsApproxSat: 0 ∈ Zariski closure of {(f₁(a), …, f_m(a)) : a ∈ F̄ⁿ} in F̄^m; reason: the closure in Definition 1.7 is the Zariski closure over F̄
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 5.6, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_ChowFormsCH_Supplement_FFCircuit
import Definitions.Def_ChowFormsCH_Supplement_IsApproxSat

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- **Theorem 5.6** (APS in CH; = Theorem 1.9, p.5) (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow
forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.49).
Let `F` be one of the fields `F_{p^a}`, `F_{p^a}(t₁, …, t_k)`, a number field `ℚ[α]`, or
`ℚ[α](t₁, …, t_k)`. Then APS over `F` lies in CH.

**Formalization Note** APS (Definition 1.7, p.5) is: given an algebraic circuit computing
`f₁, …, f_m ∈ F[x₁, …, xₙ]`, decide whether `0` lies in the Zariski closure of
`{(f₁(a), …, f_m(a)) : a ∈ F̄ⁿ}` in `F̄^m`, `F̄` the algebraic closure of `F`. The statement is per field:
for each presented field there is one language in CH (its level may depend on the field), fixed
before every input, correct on every valid circuit (constants from `F`, division gates allowed,
outputs polynomials; no bound on `n`, `m`, degrees or size). Part (1) covers `F_{p^a}` (`F_p[U]/(μ)`,
`μ` irreducible of degree `a ≥ 1`) and number fields `ℚ[α]` (`ℚ[U]/(μ)`, `μ` the minimal polynomial;
`ℚ` itself is also included) through the published `CoefficientPresentation`, `ArithmeticCircuit`,
`ValidCircuit` and `PolynomialAPS`, with constants as coordinate vectors in binary. Part (2) covers
`F(t₁, …, t_k)` for each of those base fields `F` and every `k ≥ 0`, with constants given as pairs of
polynomials in `t` in the dense representation (§5.2, p.44), included in the encoding `|C|`. -/
theorem theorem_5_6 :
    (∀ P : CoefficientPresentation, ∃ L : Language, InCountingHierarchy L ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n), ValidCircuit P C →
        (L C.encode ↔ PolynomialAPS P (circuitPolynomials P C))) ∧
    (∀ P : FunFieldPresentation, ∃ L : Language, InCountingHierarchy L ∧
      ∀ (n : ℕ) (C : FFCircuit n), ValidFFCircuit P C →
        (L C.encode ↔ IsApproxSat P.Field (ffCircuitPolynomials P C))) := by sorry

end ChowFormsCH.Supplement
