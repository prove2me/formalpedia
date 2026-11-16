-- Prove2me | Theorems.Thm_ChowFormsCH_Supplement_theorem_1_4
-- name    : ChowFormsCH.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:22:13.201563+00:00
-- url     : https://prove2.me/theorems/7657eca7-dbd7-4f7b-95ff-89959001ba13
-- title:
--   Theorem 1.4 (Degree) — $\deg V_k$, $\deg V$ and the number of isolated points of $V$ are in $\mathrm{FP}^{\mathrm{CH}}$
-- statement:
--   Let $f_1, \dots, f_m \in \mathbb{Q}[x_1, \dots, x_n]$ be polynomials represented as constant-free algebraic circuits, and let $V := V(f_1, \dots, f_m) \subseteq \mathbb{A}^n$ be their common zero set over $\overline{\mathbb{Q}}$. For $k \in \mathbb{N}$ let $V_k$ be the $k$-th equidimensional component of $V$, the union of the irreducible components of $V$ of dimension $k$. The degree of a variety is the sum of the degrees of its irreducible components.
--
--   **Theorem 1.4.** The following three functions are computable in $\mathrm{FP}^{\mathrm{CH}}$:
--
--   1. given the circuit and $k \in \mathbb{N}$, the degree $\deg V_k$;
--   2. given the circuit, the degree $\deg V$;
--   3. given the circuit, the number of isolated points of $V$.
--
--   Here $\mathrm{FP}^{\mathrm{CH}}$ is the class of functions computable in deterministic polynomial time with an oracle for a language in CH. The previous best upper bound for computing the degree of a variety was FPSPACE.
--
--   **Formalization Note** Each part is a separate existential: a language $A$ in CH and a function $g$ computed by a polynomial-time machine with oracle $A$, fixed before every input, with $g$ (`C.encode ++ encodeNat k`, resp. `C.encode`) equal to the binary encoding of the value for every valid constant-free rational circuit $C$ in $n$ variables. An empty $V_k$ has degree $0$. The isolated points are the points of the $0$-dimensional components.
--
--   Differences from the source:
--
--   - encoding: computable in FP^CH (input format not fixed) → a language A in CH and a function g computed by one deterministic polynomial-time machine with oracle A, both fixed before every input, with g returning the binary encoding of the value on every encoded valid input; reason: the definition of FP^CH; the published FunctionInPWithOracle reads the output from the output tape
--   - reading: forms (polynomials) given by constant-free algebraic circuits → valid constant-free circuits in the sense of Definition 2.6: constants 0, +1, −1 only, division gates allowed (no division by zero in ℚ(x), every output a polynomial); no weakly-division-free hypothesis; reason: the theorem says only 'constant-free algebraic circuits' (Definition 2.6, p.11, which includes ÷ gates); weakly division-free is a hypothesis of Corollaries 4.11–4.13 only, so the broader input class is taken, never the narrower one
--   - encoding: gates +, ×, ÷ (Definition 2.6) → the published circuit model, which also has a − gate; reason: x − y = x + (−1)·y with the allowed constant −1, so the class of computed polynomials and circuit sizes change by a constant factor only
--   - encoding: V = V(f₁, …, f_m) ⊆ Aⁿ, its k-th (dimension-k) equidimensional component → zeroSet in AffSp (Fin n) ℚ̄ with the Zariski topology; pureDimPart V k, the union of the irreducible components of topological Krull dimension k (possibly empty); reason: the base mission's published conventions; ℚ̄ is the algebraic closure fixed in §2.1, p.8
--   - encoding: degree of a variety (sum of the degrees of its irreducible components, §2.1 p.8); the number of isolated points of V → affDegree (Heintz degree of each component, summed); the cardinality of pureDimPart V 0, the union of the 0-dimensional components; reason: the base mission's published degree; over an algebraically closed field the isolated points of V are exactly its 0-dimensional components, finitely many
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 1.4, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_ChowFormsCH_AffSp
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_affDegree
import Definitions.Def_ChowFormsCH_Supplement_ConstantFree

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- **Theorem 1.4** (Degree) (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow
forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.4).
Given polynomials `f₁, …, f_m ∈ ℚ[x₁, …, xₙ]` represented as constant-free algebraic circuits and
`k ∈ ℕ`, one can compute the degree of the `k`-th equidimensional component of
`V := V(f₁, …, f_m)` in `FP^CH`. In particular one can compute `deg V`, as well as the number of
isolated points of `V`, in `FP^CH`.

**Formalization Note** The three conclusions are stated separately, each as membership in `FP^CH`:
a language `A` in CH and a function `g` computed by a deterministic polynomial-time machine with oracle
`A` (`FunctionInPWithOracle`), both fixed before every input, with `g` returning the binary encoding
`encodeNat` of the value on every valid (`ValidCircuit`, division gates allowed) constant-free rational
circuit `C` in `n` variables (inputs `C.encode ++ encodeNat k`, resp. `C.encode`). `V` is the affine zero
set in `Q̄ⁿ`, `Q̄` the algebraic closure of `ℚ` (`zeroSet`, Zariski topology). The `k`-th equidimensional
component is the union of the irreducible components of `V` of dimension `k` (`pureDimPart V k`,
possibly empty, of degree `0`), for every `k ∈ ℕ`. The degree is `affDegree`, the sum of the degrees of
the irreducible components (§2.1, p.8). The isolated points of `V` are the points of its
`0`-dimensional components, `pureDimPart V 0`, a finite set. -/
theorem theorem_1_4 :
    (∃ (A : Language) (g : Word → Word), InCountingHierarchy A ∧ FunctionInPWithOracle A g ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n) (k : ℕ),
        ValidCircuit CoefficientPresentation.rational C → ConstantFree C →
        g (C.encode ++ encodeNat k) =
          encodeNat (affDegree
            (pureDimPart (zeroSet (Set.range (ratPolys (AlgebraicClosure ℚ) C))) k))) ∧
    (∃ (A : Language) (g : Word → Word), InCountingHierarchy A ∧ FunctionInPWithOracle A g ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n),
        ValidCircuit CoefficientPresentation.rational C → ConstantFree C →
        g C.encode = encodeNat (affDegree (zeroSet (Set.range (ratPolys (AlgebraicClosure ℚ) C))))) ∧
    (∃ (A : Language) (g : Word → Word), InCountingHierarchy A ∧ FunctionInPWithOracle A g ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n),
        ValidCircuit CoefficientPresentation.rational C → ConstantFree C →
        g C.encode = encodeNat
          (pureDimPart (zeroSet (Set.range (ratPolys (AlgebraicClosure ℚ) C))) 0).ncard) := by sorry

end ChowFormsCH.Supplement
