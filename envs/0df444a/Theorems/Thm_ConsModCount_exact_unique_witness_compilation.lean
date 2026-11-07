-- Prove2me | Theorems.Thm_ConsModCount_exact_unique_witness_compilation
-- name    : ConsModCount.exact_unique_witness_compilation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:27.205306+00:00
-- url     : https://prove2.me/theorems/1acfd0ab-65dd-4c7d-8a99-341389eca1c6
-- title:
--   Lemma (Exact unique-witness compilation) — every $R\in\mathrm{pp}(H)$ has an exact unique-witness gadget
-- statement:
--   Let $H$ be a finite template on a finite nonempty set $D$ containing every unary subset (the standing assumption of §§10–13), and suppose $H$ has a Mal'tsev polymorphism. For every $R\in\mathrm{pp}(H)$ of arity $k$ there is an unweighted $H$-gadget with $k$ ports whose extension count is the indicator of $R$: each tuple of $R$ has exactly one satisfying assignment to all auxiliary variables, and each tuple outside $R$ has none.
--
--   The lemma lets pp-definable relations be used as constraints without changing counts, modulo any integer.
--
--   Differences from the source:
--   - reading: The gadget is effectively obtainable from a fixed pp definition of R → not a separate clause: existence of the gadget for the fixed H and R; reason: for a fixed H and a fixed R the gadget is one fixed finite object, so effectiveness has no content beyond existence; the uniform algorithmic content is the decidability of part 4 of Theorem 1
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §10, Lemma (Exact unique-witness compilation), p.14 (PDF p.15)

import Definitions.Def_ConsModCount_PP
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Lemma (Exact unique-witness compilation)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §10, p.14, PDF p.15). Under the standing
assumption of §§10–13 (`H` contains every unary subset of `D`): suppose that `H` has a Mal'tsev
polymorphism. For every fixed relation `R ∈ pp(H)` there is a finite unweighted `H`-gadget with
exposed ports for the coordinates of `R` such that each tuple in `R` has exactly one satisfying
assignment to all auxiliary variables, and each tuple outside `R` has none.

**Formalization Note.** Ports may coincide. The paper's last sentence ("The gadget is effectively
obtainable from a fixed pp definition of R") is not a separate clause: for fixed `H` and `R` the
gadget is one fixed finite object. -/
theorem exact_unique_witness_compilation {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hH : Conservative H) (hM : HasMaltsev H) {k : ℕ} (R : Set (Fin k → D))
    (hR : PPDefinable H R) :
    ∃ G : Gadget H k, IsExactGadget G R := by sorry

end ConsModCount
