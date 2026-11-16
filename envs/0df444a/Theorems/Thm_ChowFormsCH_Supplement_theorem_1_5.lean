-- Prove2me | Theorems.Thm_ChowFormsCH_Supplement_theorem_1_5
-- name    : ChowFormsCH.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:23:04.942661+00:00
-- url     : https://prove2.me/theorems/2ea2c6b8-2814-4fbe-935d-34b40affb73e
-- title:
--   Theorem 1.5 (Equidimensional Component Membership) — deciding $\alpha \in V_k$ is in CH
-- statement:
--   Let $f_1, \dots, f_m \in \mathbb{Q}[x_1, \dots, x_n]$ be polynomials represented as constant-free algebraic circuits, and let $V := V(f_1, \dots, f_m) \subseteq \mathbb{A}^n$ over $\overline{\mathbb{Q}}$. For $k \in \mathbb{N}$ the dimension-$k$ equidimensional component $V_k$ of $V$ is the union of its irreducible components of dimension $k$.
--
--   **Theorem 1.5.** The following decision problem lies in CH: given the circuit, a point $\alpha \in \mathbb{Q}^n$ and $k \in \mathbb{N}$, decide whether
--   $$\alpha \in V_k.$$
--
--   The previous best upper bound for this problem was PSPACE (Scheiblechner, 2010).
--
--   **Formalization Note** One language $L$ in CH, fixed before every input, is correct on every input `C.encode ++ encodeList encodeRat α ++ encodeNat k` with $C$ a valid constant-free rational circuit in $n$ variables. Every $k \in \mathbb{N}$ is allowed; $V_k$ may be empty.
--
--   Differences from the source:
--
--   - encoding: given f₁, …, f_m, α, k (input format not fixed) → one language (resp. one oracle machine) fixed before every input, correct on every string that is the self-delimiting binary encoding of a valid input; other strings are unconstrained; reason: the standard meaning of a decision (function) problem being in CH (FP^CH); the CircuitInputs encodings are self-delimiting, so an input is read back uniquely
--   - reading: forms (polynomials) given by constant-free algebraic circuits → valid constant-free circuits in the sense of Definition 2.6: constants 0, +1, −1 only, division gates allowed (no division by zero in ℚ(x), every output a polynomial); no weakly-division-free hypothesis; reason: the theorem says only 'constant-free algebraic circuits' (Definition 2.6, p.11, which includes ÷ gates); weakly division-free is a hypothesis of Corollaries 4.11–4.13 only, so the broader input class is taken, never the narrower one
--   - encoding: gates +, ×, ÷ (Definition 2.6) → the published circuit model, which also has a − gate; reason: x − y = x + (−1)·y with the allowed constant −1, so the class of computed polynomials and circuit sizes change by a constant factor only
--   - encoding: V = V(f₁, …, f_m) ⊆ Aⁿ, its k-th (dimension-k) equidimensional component → zeroSet in AffSp (Fin n) ℚ̄ with the Zariski topology; pureDimPart V k, the union of the irreducible components of topological Krull dimension k (possibly empty); reason: the base mission's published conventions; ℚ̄ is the algebraic closure fixed in §2.1, p.8
--   - encoding: α ∈ ℚⁿ → α : Fin n → ℚ, viewed as a point of ℚ̄ⁿ through the embedding ℚ → ℚ̄; reason: the variety lives over the algebraic closure
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 1.5, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_ChowFormsCH_AffSp
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_Supplement_ConstantFree

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- **Theorem 1.5** (Equidimensional Component Membership) (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow
forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.4).
Given polynomials `f₁, …, f_m ∈ ℚ[x₁, …, xₙ]` represented as constant-free algebraic circuits,
`α ∈ ℚⁿ` and `k ∈ ℕ`, one can decide in CH whether `α` lies in the dimension-`k` equidimensional
component of `V(f₁, …, f_m)`.

**Formalization Note** One language in CH, fixed before every input, correct on every input
`C.encode ++ encodeList encodeRat α ++ encodeNat k` with `C` a valid (division gates allowed)
constant-free rational circuit in `n` variables. `V` is the affine zero set in `Q̄ⁿ`, `Q̄` the algebraic
closure of `ℚ`, with the Zariski topology; `α` is viewed as a point of `Q̄ⁿ`. The dimension-`k`
equidimensional component is the union of the irreducible components of `V` of dimension `k`
(`pureDimPart V k`, possibly empty), for every `k ∈ ℕ`. -/
theorem theorem_1_5 :
    ∃ L : Language, InCountingHierarchy L ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n) (α : Fin n → ℚ) (k : ℕ),
        ValidCircuit CoefficientPresentation.rational C → ConstantFree C →
        (L (C.encode ++ encodeList encodeRat (List.ofFn α) ++ encodeNat k) ↔
          (show AffSp (Fin n) (AlgebraicClosure ℚ) from
              fun i => algebraMap ℚ (AlgebraicClosure ℚ) (α i)) ∈
            pureDimPart (zeroSet (Set.range (ratPolys (AlgebraicClosure ℚ) C))) k) := by sorry

end ChowFormsCH.Supplement
