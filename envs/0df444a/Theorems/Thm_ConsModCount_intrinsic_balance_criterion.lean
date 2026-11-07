-- Prove2me | Theorems.Thm_ConsModCount_intrinsic_balance_criterion
-- name    : ConsModCount.intrinsic_balance_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:05.993275+00:00
-- url     : https://prove2.me/theorems/8beae7bb-46fe-415f-aa7c-64d5fc6feb85
-- title:
--   Theorem (Intrinsic balance criterion) — strong balance ⇔ no $Q_C$ is pp-definable
-- statement:
--   Let $H$ be a finite conservative template on a finite nonempty set $D$ with a Mal'tsev polymorphism. Then
--
--   $$H\ \text{is strongly balanced}\iff Q_C\notin\mathrm{pp}(H)\ \text{for every three-element } C\subseteq D \text{ and every choice of } d\in C.$$
--
--   This is the first sentence of part 3 of Theorem 1.
--
--   Differences from the source: none.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §11, Theorem (Intrinsic balance criterion), p.20 (PDF p.21)

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Theorem (Intrinsic balance criterion)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §11, p.20, PDF p.21). For a finite conservative
template `H` with a Mal'tsev polymorphism, `H` is strongly balanced if and only if `Q_C ∉ pp(H)` for
every three-element `C ⊆ D` and every doubled fibre. -/
theorem intrinsic_balance_criterion {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hH : Conservative H) (hM : HasMaltsev H) :
    StronglyBalanced H ↔
      ∀ (C : Finset D) (d : D), C.card = 3 → d ∈ C → ¬ PPDefinable H (Q C d) := by sorry

end ConsModCount
