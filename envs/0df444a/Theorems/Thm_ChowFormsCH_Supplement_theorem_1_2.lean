-- Prove2me | Theorems.Thm_ChowFormsCH_Supplement_theorem_1_2
-- name    : ChowFormsCH.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:21:27.12629+00:00
-- url     : https://prove2.me/theorems/c23ac7c3-d533-4224-9ef6-91f4a836b461
-- title:
--   Theorem 1.2 (Chow Form Coefficients) — deciding whether a coefficient of $C_{V_k}$ is zero is in CH
-- statement:
--   Let $F_1, \dots, F_m \in \mathbb{Q}[x_0, \dots, x_n]$ be forms given by constant-free algebraic circuits, $V := V(F_1, \dots, F_m) \subseteq \mathbb{P}^n$ over $\overline{\mathbb{Q}}$, $V_k$ the $k$-equidimensional component of $V$ and $C_{V_k}$ its Chow form in the variables $u_{i,j}$, $0 \le i \le k$, $0 \le j \le n$.
--
--   **Theorem 1.2.** The following decision problem lies in CH: given $V$ (the circuit), $k \in \mathbb{N}$ and an exponent vector $e \in \mathbb{N}^{(n+1)(k+1)}$, written in binary, decide whether the coefficient of the monomial
--   $$\prod_{i=0}^{k} \prod_{j=0}^{n} u_{i,j}^{\,e_{i,j}}$$
--   in $C_{V_k}$ is zero.
--
--   Zero-ness of a coefficient does not depend on the scalar normalization of $C_{V_k}$. Since $\deg C_{V_k}$ can be exponential in the input size, the exponents are given in binary. Together with Theorem 1.1 this gives CH access to the whole Chow form.
--
--   **Formalization Note** One language $L$ in CH, fixed before every input, is correct on every input `C.encode ++ encodeNat k ++ encodeList encodeNat e` with $C$ a valid constant-free rational circuit in $n+1$ variables whose outputs are homogeneous; $C_{V_k}$ is the normalized Chow form, asserted to exist.
--
--   Differences from the source:
--
--   - encoding: given V, k, e (input format not fixed) → one language (resp. one oracle machine) fixed before every input, correct on every string that is the self-delimiting binary encoding of a valid input; other strings are unconstrained; reason: the standard meaning of a decision (function) problem being in CH (FP^CH); the CircuitInputs encodings are self-delimiting, so an input is read back uniquely
--   - reading: forms (polynomials) given by constant-free algebraic circuits → valid constant-free circuits in the sense of Definition 2.6: constants 0, +1, −1 only, division gates allowed (no division by zero in ℚ(x), every output a polynomial); no weakly-division-free hypothesis; reason: the theorem says only 'constant-free algebraic circuits' (Definition 2.6, p.11, which includes ÷ gates); weakly division-free is a hypothesis of Corollaries 4.11–4.13 only, so the broader input class is taken, never the narrower one
--   - encoding: gates +, ×, ÷ (Definition 2.6) → the published circuit model, which also has a − gate; reason: x − y = x + (−1)·y with the allowed constant −1, so the class of computed polynomials and circuit sizes change by a constant factor only
--   - encoding: V ⊆ Pⁿ over the algebraic closure, V_k its k-equidimensional component, C_{V_k} its Chow form → V = projZero on the punctured cone ℚ̄^{n+1} \ {0}; V_k = equidimComponent V k (union of the irreducible components of projective dimension k, possibly empty); C_{V_k} the normalized Chow form (lex-leading coefficient 1), an empty V_k having Chow form 1; reason: the base mission's published conventions; vanishing of C_{V_k} at a point, and of a coefficient, does not depend on the nonzero scalar normalizing C_{V_k}
--   - reading: setup: 0 ≤ k ≤ n; theorem: k ∈ ℕ → every k ∈ ℕ; for k > n, V_k = ∅ and C_{V_k} = 1; reason: the theorem quantifies k ∈ ℕ; the broader reading is taken, and it agrees with the setup on 0 ≤ k ≤ n
--   - encoding: e ∈ ℕ^{(n+1)(k+1)}, the exponent vector of a monomial in the variables of C_{V_k} → e : Fin (k+1) × Fin (n+1) → ℕ arbitrary, every entry in binary, listed row by row; the monomial ∏ u_{i,j}^{e_{i,j}}; reason: every exponent vector names a monomial in the u_{i,j}; one of the wrong total degree has coefficient zero
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 1.2, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_IsChowForm
import Definitions.Def_ChowFormsCH_Supplement_ConstantFree

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- **Theorem 1.2** (Chow Form Coefficients) (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow
forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.4).
In the setup of Theorem 1.1, let `k ∈ ℕ` and let `e ∈ ℕ^{(n+1)(k+1)}` be the exponent vector of a
monomial in the variables `u_{i,j}` of `C_{V_k}`. Given `V`, `k`, `e`, one can decide in CH whether the
coefficient of the monomial `∏ u_{i,j}^{e_{i,j}}` in `C_{V_k}` is zero.

**Formalization Note** Same promise and conventions as `theorem_1_1`: one language in CH, correct on
every valid constant-free rational circuit in `n + 1` variables with homogeneous outputs; `V` over the
algebraic closure of `ℚ`; `V_k = equidimComponent V k`; every `k ∈ ℕ`; `C_{V_k}` the normalized Chow
form (zero-ness of a coefficient does not depend on the normalization). The input string is
`C.encode ++ encodeNat k ++ encodeList encodeNat e`, with `e = (e_{i,j})` listed row by row and every
exponent in binary; `e` is arbitrary, so a monomial of the wrong degree has coefficient zero. -/
theorem theorem_1_2 :
    ∃ L : Language, InCountingHierarchy L ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit (n + 1)) (k : ℕ) (e : Fin (k + 1) × Fin (n + 1) → ℕ),
        ValidCircuit CoefficientPresentation.rational C → ConstantFree C →
        (∀ j, ∃ d : ℕ, (ratPolysQ C j).IsHomogeneous d) →
        ∃ Cf : MvPolynomial (Fin (k + 1) × Fin (n + 1)) (AlgebraicClosure ℚ),
          IsNormalizedChowForm
            (equidimComponent (projZero (Set.range (ratPolys (AlgebraicClosure ℚ) C))) k) k Cf ∧
          (L (C.encode ++ encodeNat k ++ encodeList encodeNat (gridList e)) ↔
            MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) Cf = 0) := by sorry

end ChowFormsCH.Supplement
