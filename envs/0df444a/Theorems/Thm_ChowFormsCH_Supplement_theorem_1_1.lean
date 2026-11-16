-- Prove2me | Theorems.Thm_ChowFormsCH_Supplement_theorem_1_1
-- name    : ChowFormsCH.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:20:44.248292+00:00
-- url     : https://prove2.me/theorems/5ee19566-7b1d-4ea9-b3e7-322044d3ca21
-- title:
--   Theorem 1.1 (Zeros of Chow Form) — deciding $C_{V_k}(a) = 0$ is in CH
-- statement:
--   Let $F_1, \dots, F_m \in \mathbb{Q}[x_0, \dots, x_n]$ be forms given by constant-free algebraic circuits, and let $V := V(F_1, \dots, F_m) \subseteq \mathbb{P}^n$ be the projective variety they define over the algebraic closure $\overline{\mathbb{Q}}$. For $k \in \mathbb{N}$ let $V_k$ be the $k$-equidimensional component of $V$ (the union of its irreducible components of dimension $k$) and $C_{V_k}$ its Chow form, a polynomial in the $(k+1)(n+1)$ variables $u_{i,j}$, $0 \le i \le k$, $0 \le j \le n$.
--
--   **Theorem 1.1.** The following decision problem lies in the counting hierarchy CH: given $V$ (that is, the circuit), $k$ and a point $a \in \mathbb{Q}^{(n+1)(k+1)}$, decide whether
--   $$C_{V_k}(a) = 0.$$
--
--   A circuit is constant-free when its only constants are $0$, $+1$ and $-1$; division gates are allowed, provided no division by zero occurs in $\mathbb{Q}(x)$. Since $C_{V_k}$ is defined only up to a nonzero scalar, its vanishing at $a$ is a well-defined property of $V$, $k$ and $a$. The theorem is one of the paper's main consequences of the Chow-form circuits of Theorem 4.9.
--
--   **Formalization Note** One language $L$ in CH, fixed before every input, must answer correctly on every input string `C.encode ++ encodeNat k ++ encodeList encodeRat a` in which $C$ is a valid constant-free rational circuit in $n+1$ variables with homogeneous outputs; the statement also asserts that the normalized Chow form exists. Projective space is the punctured affine cone, and an empty $V_k$ (for instance $k > n$) has Chow form $1$.
--
--   Differences from the source:
--
--   - encoding: given V, k, a (input format not fixed) → one language (resp. one oracle machine) fixed before every input, correct on every string that is the self-delimiting binary encoding of a valid input; other strings are unconstrained; reason: the standard meaning of a decision (function) problem being in CH (FP^CH); the CircuitInputs encodings are self-delimiting, so an input is read back uniquely
--   - reading: forms (polynomials) given by constant-free algebraic circuits → valid constant-free circuits in the sense of Definition 2.6: constants 0, +1, −1 only, division gates allowed (no division by zero in ℚ(x), every output a polynomial); no weakly-division-free hypothesis; reason: the theorem says only 'constant-free algebraic circuits' (Definition 2.6, p.11, which includes ÷ gates); weakly division-free is a hypothesis of Corollaries 4.11–4.13 only, so the broader input class is taken, never the narrower one
--   - encoding: gates +, ×, ÷ (Definition 2.6) → the published circuit model, which also has a − gate; reason: x − y = x + (−1)·y with the allowed constant −1, so the class of computed polynomials and circuit sizes change by a constant factor only
--   - encoding: V ⊆ Pⁿ over the algebraic closure, V_k its k-equidimensional component, C_{V_k} its Chow form → V = projZero on the punctured cone ℚ̄^{n+1} \ {0}; V_k = equidimComponent V k (union of the irreducible components of projective dimension k, possibly empty); C_{V_k} the normalized Chow form (lex-leading coefficient 1), an empty V_k having Chow form 1; reason: the base mission's published conventions; vanishing of C_{V_k} at a point, and of a coefficient, does not depend on the nonzero scalar normalizing C_{V_k}
--   - reading: setup: 0 ≤ k ≤ n; theorem: k ∈ ℕ → every k ∈ ℕ; for k > n, V_k = ∅ and C_{V_k} = 1; reason: the theorem quantifies k ∈ ℕ; the broader reading is taken, and it agrees with the setup on 0 ≤ k ≤ n
--   - encoding: a ∈ ℚ^{(n+1)(k+1)} → a : Fin (k+1) × Fin (n+1) → ℚ, the coordinate a_{i,j} paired with the Chow-form variable u_{i,j}, listed row by row in the input; reason: the paper's variable order u_{0,0}, …, u_{0,n}, u_{1,0}, … (§3.1, p.21)
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 1.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_IsChowForm
import Definitions.Def_ChowFormsCH_Supplement_ConstantFree

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- **Theorem 1.1** (Zeros of Chow Form) (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow
forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.4).
Let `F₁, …, F_m ∈ ℚ[x₀, …, xₙ]` be forms given by constant-free algebraic circuits, let
`V := V(F₁, …, F_m) ⊆ Pⁿ`, let `V_k` be the `k`-equidimensional component of `V` and `C_{V_k}` its
Chow form. Given `V`, `k ∈ ℕ` and `a ∈ ℚ^{(n+1)(k+1)}`, one can decide whether `C_{V_k}(a) = 0` in CH.

**Formalization Note** One language `L` in the counting hierarchy (`InCountingHierarchy`, fixed
before every input) is correct on every input `(C, k, a)` that satisfies the promise: `C` is a valid
(`ValidCircuit`: no division by zero in `ℚ(x)`, polynomial outputs) constant-free rational circuit
in `n + 1` variables whose outputs `F₁, …, F_m` (all of them, `m` = number of output gates, possibly
`0`) are homogeneous. The input string is `C.encode ++ encodeNat k ++ encodeList encodeRat a`, the
point `a = (a_{i,j})`, `0 ≤ i ≤ k`, `0 ≤ j ≤ n`, listed row by row. Division gates are allowed, as in
Definition 2.6. `V` is the projective zero set over the algebraic closure of `ℚ` (`projZero` on the
punctured cone) and `V_k = equidimComponent V k` (empty if `V` has no `k`-dimensional component; then
its Chow forms are the nonzero constants). `k` ranges over all of `ℕ`. `C_{V_k}` is the normalized Chow
form; whether it vanishes at `a` does not depend on the normalization. -/
theorem theorem_1_1 :
    ∃ L : Language, InCountingHierarchy L ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit (n + 1)) (k : ℕ) (a : Fin (k + 1) × Fin (n + 1) → ℚ),
        ValidCircuit CoefficientPresentation.rational C → ConstantFree C →
        (∀ j, ∃ e : ℕ, (ratPolysQ C j).IsHomogeneous e) →
        ∃ Cf : MvPolynomial (Fin (k + 1) × Fin (n + 1)) (AlgebraicClosure ℚ),
          IsNormalizedChowForm
            (equidimComponent (projZero (Set.range (ratPolys (AlgebraicClosure ℚ) C))) k) k Cf ∧
          (L (C.encode ++ encodeNat k ++ encodeList encodeRat (gridList a)) ↔
            MvPolynomial.eval (fun ij => algebraMap ℚ (AlgebraicClosure ℚ) (a ij)) Cf = 0) := by sorry

end ChowFormsCH.Supplement
