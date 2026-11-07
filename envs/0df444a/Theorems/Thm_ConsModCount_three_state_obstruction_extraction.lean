-- Prove2me | Theorems.Thm_ConsModCount_three_state_obstruction_extraction
-- name    : ConsModCount.three_state_obstruction_extraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:06.605471+00:00
-- url     : https://prove2.me/theorems/b0844851-04d5-4b5c-9ec9-dc11ca859f20
-- title:
--   Theorem (Three-state obstruction extraction) — failure of strong balance yields $Q_C\in\mathrm{pp}(H)$
-- statement:
--   Let $H$ be a finite template on a finite nonempty set $D$ containing every unary subset. If $H$ has a Mal'tsev polymorphism and is not strongly balanced, then there are a three-element $C\subseteq D$ and $d\in C$ such that
--
--   $$Q_C\in\mathrm{pp}(H),$$
--
--   where $Q_C$ is taken with singleton fibre $\{d\}$, and $Q_C$ has an exact unique-witness $H$-gadget.
--
--   Together with the converse in the intrinsic balance criterion this characterizes strong balance on the conservative Mal'tsev branch.
--
--   Differences from the source: none.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §11, Theorem (Three-state obstruction extraction), p.19 (PDF p.20)

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Theorem (Three-state obstruction extraction)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §11, p.19, PDF p.20). Under the standing
assumption of §§10–13 (`H` conservative): if `H` has a Mal'tsev polymorphism and is not strongly
balanced, then `Q_C ∈ pp(H)` for some three-element subset `C ⊆ D` and some choice of its doubled
fibre. Moreover, `Q_C` has an exact unique-witness `H`-gadget.

**Formalization Note.** The doubled fibre is `C \ {d}`; the choice is the singleton `d ∈ C`. -/
theorem three_state_obstruction_extraction {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hH : Conservative H) (hM : HasMaltsev H) (hSB : ¬ StronglyBalanced H) :
    ∃ (C : Finset D) (d : D), C.card = 3 ∧ d ∈ C ∧ PPDefinable H (Q C d) ∧
      ∃ G : Gadget H 4, IsExactGadget G (Q C d) := by sorry

end ConsModCount
