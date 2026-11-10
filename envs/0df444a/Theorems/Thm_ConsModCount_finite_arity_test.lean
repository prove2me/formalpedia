-- Prove2me | Theorems.Thm_ConsModCount_finite_arity_test
-- name    : ConsModCount.finite_arity_test
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T07:29:16.229976+00:00
-- url     : https://prove2.me/theorems/985ea327-2d74-4b22-ad6f-98d1eaddf194
-- title:
--   Lemma (Finite arity test for quotient parity) — $Q_C\in\mathrm{pp}(H)$ iff all 41-ary polymorphisms preserve it
-- statement:
--   Let $H$ be a finite template on a finite nonempty set $D$ containing every unary subset, $C\subseteq D$ a three-element set and $d\in C$. Then
--
--   $$Q_C\in\mathrm{pp}(H)\iff\text{every 41-ary polymorphism of } H \text{ preserves } Q_C.$$
--
--   Since $D^{D^{41}}$ is finite, this makes $Q_C\in\mathrm{pp}(H)$ decidable.
--
--   Differences from the source: none.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §13, Lemma (Finite arity test for quotient parity), p.23 (PDF p.24)

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Lemma (Finite arity test for quotient parity)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §13, p.23, PDF p.24). Under the standing
assumption of §§10–13 (`H` conservative): a given relation `Q_C` belongs to `pp(H)` if and only if
every 41-ary polymorphism of `H` preserves `Q_C`. -/
theorem finite_arity_test {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D) (hH : Conservative H)
    (C : Finset D) (d : D) (hC : C.card = 3) (hd : d ∈ C) :
    PPDefinable H (Q C d) ↔
      ∀ f : (Fin 41 → D) → D, IsPolymorphism H f → Preserves f (Q C d) := by sorry

end ConsModCount
