-- Prove2me | Theorems.Thm_ChowFormsCH_Supplement_theorem_1_6
-- name    : ChowFormsCH.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:23:37.889072+00:00
-- url     : https://prove2.me/theorems/e721443d-524c-4167-806b-b7e814525024
-- title:
--   Theorem 1.6 (Image Closure Membership) — deciding $\alpha \in \overline{\Phi_h(V)}$ is in CH
-- statement:
--   Let $p \in \mathbb{N}$ and let $f_1, \dots, f_m, h_1, \dots, h_p \in \mathbb{Q}[x_1, \dots, x_n]$ be represented as constant-free algebraic circuits. Let $V := V(f_1, \dots, f_m) \subseteq \mathbb{C}^n$ and let $\Phi_h : \mathbb{C}^n \to \mathbb{C}^p$ be the polynomial map $\Phi_h(x) = (h_1(x), \dots, h_p(x))$.
--
--   **Theorem 1.6.** The following promise problem lies in CH: given a point $\alpha \in \mathbb{Q}^p$ and the circuits for $f_1, \dots, f_m$ and $h_1, \dots, h_p$, where $V$ is irreducible and of dimension $p - 1$, decide whether
--   $$\alpha \in \overline{\Phi_h(V)}.$$
--
--   No condition is placed on the dimension of the image $\Phi_h(V)$. Image closure membership includes the computation of transcendence degree and approximate polynomial satisfiability over $\mathbb{Q}$ (Remark 1.8) as special cases.
--
--   **Formalization Note** One language $L$ in CH, fixed before every input, is correct on every input `Cf.encode ++ Ch.encode ++ encodeList encodeRat α` where both circuits are valid and constant-free in the same $n$ variables, $p$ is the number of outputs of the circuit for $h$, and $V$ is irreducible with $\dim V + 1 = p$. On inputs that break this promise the language is unconstrained. $\mathbb{C}^n$ and $\mathbb{C}^p$ carry the Zariski topology, and the closure is the Zariski closure.
--
--   Differences from the source:
--
--   - encoding: given α and f₁, …, f_m, h₁, …, h_p (input format not fixed) → one language (resp. one oracle machine) fixed before every input, correct on every string that is the self-delimiting binary encoding of a valid input; other strings are unconstrained; reason: the standard meaning of a decision (function) problem being in CH (FP^CH); the CircuitInputs encodings are self-delimiting, so an input is read back uniquely
--   - reading: forms (polynomials) given by constant-free algebraic circuits → valid constant-free circuits in the sense of Definition 2.6: constants 0, +1, −1 only, division gates allowed (no division by zero in ℚ(x), every output a polynomial); no weakly-division-free hypothesis; reason: the theorem says only 'constant-free algebraic circuits' (Definition 2.6, p.11, which includes ÷ gates); weakly division-free is a hypothesis of Corollaries 4.11–4.13 only, so the broader input class is taken, never the narrower one
--   - encoding: gates +, ×, ÷ (Definition 2.6) → the published circuit model, which also has a − gate; reason: x − y = x + (−1)·y with the allowed constant −1, so the class of computed polynomials and circuit sizes change by a constant factor only
--   - encoding: p ∈ ℕ and h₁, …, h_p → p is the number of output gates of the circuit for h; reason: the circuit lists h₁, …, h_p, so p is read off the input
--   - encoding: V(f₁, …, f_m) ⊆ ℂⁿ irreducible and of dimension p − 1 → IsIrreducible V (in particular nonempty) for the Zariski topology of ℂⁿ, and topologicalKrullDim V + 1 = p; reason: dimension is the Krull dimension of the Zariski topology; the form dim V + 1 = p avoids natural-number subtraction
--   - encoding: the closure of Φ_h(V) → the Zariski closure in ℂᵖ; reason: Φ_h(V) is constructible (Chevalley), and for a constructible subset of ℂᵖ the Zariski and Euclidean closures coincide, so both readings give the same set
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 1.6, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_ChowFormsCH_AffSp
import Definitions.Def_ChowFormsCH_Supplement_ConstantFree

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- **Theorem 1.6** (Image Closure Membership) (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow
forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.5).
Let `p ∈ ℕ` and let `f₁, …, f_m ∈ ℚ[x₁, …, xₙ]`, represented as constant-free algebraic circuits, be
such that the variety `V(f₁, …, f_m)` is irreducible and of dimension `p − 1`. Let
`h₁, …, h_p ∈ ℚ[x₁, …, xₙ]`, represented as constant-free algebraic circuits, define the polynomial map
`Φ_h : ℂⁿ → ℂᵖ`. Given `α ∈ ℚᵖ` and `f₁, …, f_m, h₁, …, h_p` as above, one can decide in CH whether `α`
lies in the closure of `Φ_h(V(f₁, …, f_m))`.

**Formalization Note** A promise problem: one language in CH, fixed before every input, correct on
every input `C_f.encode ++ C_h.encode ++ encodeList encodeRat α` where `C_f`, `C_h` are valid (division
gates allowed) constant-free rational circuits in the same `n` variables, `p` is the number of output
gates of `C_h`, and `V := V(f) ⊆ ℂⁿ` is irreducible (in particular nonempty) with
`dim V + 1 = p`, i.e. `dim V = p − 1` without natural-number truncation. No hypothesis on the
dimension of the image is made. `ℂⁿ` and `ℂᵖ` carry the Zariski topology (`AffSp`), the dimension is
the topological Krull dimension of `V`, and the closure is the Zariski closure in `ℂᵖ` (which equals the
Euclidean closure for the constructible set `Φ_h(V)`). -/
theorem theorem_1_6 :
    ∃ L : Language, InCountingHierarchy L ∧
      ∀ (n : ℕ) (Cf Ch : ArithmeticCircuit n) (α : Fin Ch.outputs.length → ℚ),
        ValidCircuit CoefficientPresentation.rational Cf → ConstantFree Cf →
        ValidCircuit CoefficientPresentation.rational Ch → ConstantFree Ch →
        IsIrreducible (zeroSet (Set.range (ratPolys ℂ Cf))) →
        topologicalKrullDim (zeroSet (Set.range (ratPolys ℂ Cf))) + 1 =
          (Ch.outputs.length : WithBot ℕ∞) →
        (L (Cf.encode ++ Ch.encode ++ encodeList encodeRat (List.ofFn α)) ↔
          (show AffSp (Fin Ch.outputs.length) ℂ from fun j => (α j : ℂ)) ∈
            closure ((fun x : AffSp (Fin n) ℂ =>
                (show AffSp (Fin Ch.outputs.length) ℂ from
                  fun j => MvPolynomial.eval (show Fin n → ℂ from x) (ratPolys ℂ Ch j))) ''
              zeroSet (Set.range (ratPolys ℂ Cf)))) := by sorry

end ChowFormsCH.Supplement
